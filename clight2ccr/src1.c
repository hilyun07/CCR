#include <stdio.h>

extern int w;
extern int g(int);
static int t = 1;
int v;

int main(){
  t = 2;
  printf("[main] w : %d\n", w);
  printf("[main] v : %d\n", v);
  v = g(8);
  w = 0;
  printf("[main] w : %d\n", w);
  printf("[main] v : %d\n", v);
  return 0;
}
  
  
