#include <vector>
#include <iostream>

void push_all(const std::vector<int>& from, std::vector<int>& to) {
    for (int elem : from) {
        to.push_back(elem);
    }
}

int main() {
  std::vector<int> v(3, 42); // v = {42, 42, 42}

  push_all(v, v); // aliasing!

  for (int elem : v) {
    std::cout << elem << " ";
  }

  std::cout << std::endl;

  return 0;
}
