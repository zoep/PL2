#include <stdio.h>

int buf[8] = {1,2,3,4,5,6,7,8};
int secret = 42;

int main() {

  int i;

  printf("Enter a number:\n");

  scanf("%d", &i);

  printf("%d\n", buf[i]);

}


