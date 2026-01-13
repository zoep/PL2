#include <stdio.h>

char buf[8];
int secret;

int main() {

  secret = 0;

  printf("Give me a string: ");
  scanf("%s", buf);

  printf("%d\n", secret);

}
