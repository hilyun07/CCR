#include <stdio.h>

extern char* w;
extern void g(void);

char* v = "I'm v and in src1.";

int main(){
  puts(v);
  puts(w);
  g();
  puts(v);
  puts(w);
  return 0;
}
  
  
