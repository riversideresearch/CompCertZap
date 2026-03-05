#!/usr/bin/env python3
"""Query proof goals at a source position via coq-lsp."""

import argparse
import json
import os
import pathlib
import select
import subprocess
import sys
import time
from typing import Any, Dict, Optional


def find_project_root(path: pathlib.Path) -> pathlib.Path:
    for directory in [path.parent, *path.parent.parents]:
        if (directory / "_CoqProject").exists() or (directory / "_RocqProject").exists():
            return directory
    return pathlib.Path.cwd()


class LspClient:
    def __init__(self, cmd: list[str]) -> None:
        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False,
        )
        if self.proc.stdin is None or self.proc.stdout is None:
            raise RuntimeError("failed to create stdio pipes for coq-lsp")
        self._stdin = self.proc.stdin
        self._stdout = self.proc.stdout
        self._fd = self._stdout.fileno()
        self._next_id = 1

    def _read_message(self, timeout_s: float) -> Dict[str, Any]:
        end = time.monotonic() + timeout_s
        header = bytearray()
        marker = b"\r\n\r\n"
        while marker not in header:
            remaining = end - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("timed out waiting for LSP header")
            ready, _, _ = select.select([self._fd], [], [], remaining)
            if not ready:
                continue
            chunk = os.read(self._fd, 1)
            if not chunk:
                raise RuntimeError("coq-lsp closed stdout")
            header.extend(chunk)

        raw_header, body = header.split(marker, 1)
        content_length: Optional[int] = None
        for line in raw_header.decode("ascii", errors="replace").split("\r\n"):
            if line.lower().startswith("content-length:"):
                content_length = int(line.split(":", 1)[1].strip())
                break
        if content_length is None:
            raise RuntimeError("missing Content-Length in LSP header")

        while len(body) < content_length:
            remaining = end - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("timed out reading LSP body")
            ready, _, _ = select.select([self._fd], [], [], remaining)
            if not ready:
                continue
            chunk = os.read(self._fd, content_length - len(body))
            if not chunk:
                raise RuntimeError("coq-lsp closed stdout while reading body")
            body.extend(chunk)

        return json.loads(body.decode("utf-8"))

    def _send(self, msg: Dict[str, Any]) -> None:
        payload = json.dumps(msg, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        header = f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii")
        self._stdin.write(header)
        self._stdin.write(payload)
        self._stdin.flush()

    def notify(self, method: str, params: Dict[str, Any]) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method: str, params: Dict[str, Any], timeout_s: float) -> Dict[str, Any]:
        req_id = self._next_id
        self._next_id += 1
        self._send({"jsonrpc": "2.0", "id": req_id, "method": method, "params": params})
        while True:
            msg = self._read_message(timeout_s)
            if msg.get("id") == req_id:
                return msg

    def close(self) -> None:
        try:
            try:
                shutdown = self.request("shutdown", {}, timeout_s=5.0)
                if "error" in shutdown:
                    pass
            except Exception:
                pass
        finally:
            try:
                self.notify("exit", {})
            except Exception:
                pass
            try:
                self.proc.wait(timeout=2.0)
            except subprocess.TimeoutExpired:
                self.proc.kill()


def main() -> int:
    parser = argparse.ArgumentParser(description="Query coq-lsp proof goals at a file position")
    parser.add_argument("file", help="Path to .v file")
    parser.add_argument("line", type=int, help="1-based line")
    parser.add_argument("column", type=int, nargs="?", default=1, help="1-based column")
    parser.add_argument("--mode", choices=["Prev", "After"], default="After")
    parser.add_argument("--pp-format", choices=["Str", "Pp", "Box"], default="Str")
    parser.add_argument("--no-compact", action="store_true")
    parser.add_argument("--timeout", type=float, default=120.0, help="Response timeout in seconds")
    parser.add_argument("--root", default=None, help="Project root (defaults to nearest _CoqProject)")
    parser.add_argument("--trace", action="store_true", help="Enable coq-lsp wire trace")
    args = parser.parse_args()

    file_path = pathlib.Path(args.file).resolve()
    if not file_path.exists():
        print(f"error: file not found: {file_path}", file=sys.stderr)
        return 2
    if args.line < 1 or args.column < 1:
        print("error: line and column must be >= 1", file=sys.stderr)
        return 2

    root = pathlib.Path(args.root).resolve() if args.root else find_project_root(file_path)
    uri = file_path.as_uri()
    text = file_path.read_text(encoding="utf-8")

    cmd = ["coq-lsp"]
    if args.trace:
        cmd.append("--lsp_trace")

    client = LspClient(cmd)
    try:
        init_params = {
            "processId": None,
            "clientInfo": {"name": "coq_lsp_goals.py", "version": "1"},
            "rootUri": root.as_uri(),
            "capabilities": {},
            "workspaceFolders": [{"uri": root.as_uri(), "name": root.name}],
            "initializationOptions": {"check_only_on_request": True},
        }
        init = client.request("initialize", init_params, timeout_s=args.timeout)
        if "error" in init:
            print(json.dumps(init["error"], indent=2), file=sys.stderr)
            return 1

        client.notify("initialized", {})
        client.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": uri,
                    "languageId": "coq",
                    "version": 1,
                    "text": text,
                }
            },
        )

        goals_params = {
            "textDocument": {"uri": uri, "version": 1},
            "position": {"line": args.line - 1, "character": args.column - 1},
            "pp_format": args.pp_format,
            "compact": not args.no_compact,
            "mode": args.mode,
        }
        goals = client.request("proof/goals", goals_params, timeout_s=args.timeout)
        if "error" in goals:
            print(json.dumps(goals["error"], indent=2), file=sys.stderr)
            return 1
        print(json.dumps(goals.get("result", {}), indent=2, ensure_ascii=False))
        return 0
    except TimeoutError as err:
        print(f"error: {err}. try a larger --timeout value.", file=sys.stderr)
        return 1
    except RuntimeError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    finally:
        client.close()


if __name__ == "__main__":
    raise SystemExit(main())
