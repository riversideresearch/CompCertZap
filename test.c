#include <stdio.h>

static unsigned long long iters = 1000000;

unsigned long long int search_for_corruption(void);
unsigned long long int search_for_corruption(void) {
  volatile unsigned int x0;
  volatile unsigned int x1;
  volatile unsigned int x2;
  volatile unsigned int x3;
  volatile unsigned int x4;
  volatile unsigned int x5;
  volatile unsigned int x6;
  volatile unsigned int x7;  
  x0 = 1;
  x1 = 2;
  x2 = 4;
  x3 = 8;
  x4 = 16;
  x5 = 32;
  x6 = 64;
  x7 = 128;
  unsigned int num_faults = 0;
  for (int i = 0; i < iters; i++) {
    unsigned int t0=x0, t1=x1, t2=x2, t3=x3;
    x0 = x7;
    x1 = x6;
    x2 = x5;
    x3 = x4;
    x4 = t3;
    x5 = t2;
    x6 = t1;
    x7 = t0;
    if ((x0^x1^x2^x3^x4^x5^x6^x7) != 255) num_faults++;
  }
  return num_faults;
}

int main(void);
int main(void) {
  return search_for_corruption();
}
