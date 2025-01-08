#include <stdio.h>

char buf[8];
int secret;

int main() {

  secret = 0;

  scanf("Give me a string: %s", buf);

  printf("%d\n", secret);

}
