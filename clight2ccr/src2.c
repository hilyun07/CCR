#include <stdio.h>

extern int v;

int w = 2;

int g (int i){
  v = i*i;
  w = i*i*i;
  printf("[g] w : %d\n", w);
  printf("[g] v : %d\n", v);
  return v;
}
  
  
