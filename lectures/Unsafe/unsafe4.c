#include <stdio.h>

// Adjusted function to overwrite return address
int function() {
  char buf[4];  

  buf[0] = 'a';
  buf[1] = 'b';
  buf[2] = 'c';
  buf[3] = '\0';
    
  printf("%s\n", buf);

  *((int *) &buf + 3) += 0x8;

  return 1;
}

int main() {
  int x;

  x = 0;
  function();
  x = 42;

  printf("%d\n", x);
}
