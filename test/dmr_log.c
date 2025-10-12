// Test DMR detection with handler functions that print the offending
// registers and their contents and terminate the program.

// To test fault detection with this program, you need to either
// induce a fault in simulation (e.g., with spike) or modify the
// builtins to pretend that a fault has occurred in [f] or [main].

#include <stdio.h>
#include <stdlib.h>

void __fault_int(int reg1, int reg2, int val1, int val2) {
  printf("reg %d = %d <> reg %d = %d\n", reg1, val1, reg2, val2);
  exit(-1);
}

void __fault_long(int reg1, int reg2, long val1, long val2) {
  printf("reg %d = %ld <> reg %d = %ld\n", reg1, val1, reg2, val2);
  exit(-1);
}

void __fault_single(int reg1, int reg2, float val1, float val2) {
  printf("reg %d = %f <> reg %d = %f\n", reg1, val1, reg2, val2);
  exit(-1);
}

void __fault_float(int reg1, int reg2, double val1, double val2) {
  printf("reg %d = %lf <> reg %d = %lf\n", reg1, val1, reg2, val2);
  exit(-1);
}

int f(int x) {
  return x + 1;
}

int main() {
  return f(1);
}
