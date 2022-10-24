#include <string.xh>

int main(int argc, char **argv) {
  string (*fn)() = show; // Illegal use of `show` as a value
  return 0;
}
