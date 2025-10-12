## Make RISC-V tools directory
```bash
sudo mkdir /opt/riscv && \
sudo chown $(whoami):$(whoami) /opt/riscv
```

## Install RISC-V cross-compiler
```bash
sudo apt-get install autoconf automake autotools-dev curl python3 python3-pip python3-tomli libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev ninja-build git cmake libglib2.0-dev libslirp-dev && \
git clone https://github.com/riscv-collab/riscv-gnu-toolchain.git && \
cd riscv-gnu-toolchain && \
./configure --prefix=/opt/riscv && \
make linux -j$(nproc)
```

## Install RISC-V proxy kernel
```bash
git clone https://github.com/riscv-software-src/riscv-pk.git && \
cd riscv-pk && \
mkdir build && cd build && \
../configure --prefix=/opt/riscv --host=riscv64-unknown-linux-gnu && \
make install -j$(nproc)
```

## Install spike
```bash
sudo apt install device-tree-compiler libboost-regex-dev libboost-system-dev && \
git clone ssh://git@ssh.bitbucket.riversideresearch.org:7999/radhs/riscv-isa-sim.git && \
cd riscv-isa-sim && git switch replicate && mkdir build && cd build && \
../configure --prefix=/opt/riscv/ --with-target=riscv64-unknown-linux-gnu && \
make install -j$(nproc)
```

Add to `~/.bashrc`:
```bash
export PATH="/opt/riscv/bin:$PATH"
```

## Run spike
```bash
spike pk <prog> <arg*>
```

## Build CompCert with TMR pass
```bash
git clone ssh://git@ssh.bitbucket.riversideresearch.org:7999/radhs/compcert.git && \
cd compcert && git switch replicate && \
./configure -toolprefix riscv64-unknown-linux-gnu- riscv64-linux && \
make -j$(nproc)
```

`sudo make install` to install globally.
