#include <stdio.h>

void foo() {

  char buf[4];
  scanf("%s", buf);
  
}
  
int main() {

  int y = 0;
  int x = 42;

  foo();
  
  printf("x is %d\n", x);

  x += 1;

  printf("x is %d\n", x);

  x += 1;

  printf("x is %d\n", x);

  x += 1;  

  printf("x is %d\n", x);

}
