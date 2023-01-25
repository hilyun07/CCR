#include <stdio.h>

extern char* v;

char* w = "I'm w and in src1.";

void g (){
  v = "I'm v and in src2.";
  w = "I'm w and in src2.";
}
  
  
