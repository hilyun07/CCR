#include <stdio.h>

extern char* v;

char* w = "I'm w and in src1.";
static char* s = "ABC";

void g (){
  v = "I'm v and in src2.";
  w = "I'm w and in src2.";
  puts(s);
}
  
  
