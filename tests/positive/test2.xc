#include <string.xh>
#include <stdio.h>
#include <stdlib.h>

struct foo {
  int x;
  float y;
  string z;
};

size_t showAsInt(char *buf, float x) {
  return sprintf(buf, "%d", (int)x);
}

int main() {
  struct foo thing = {1, 2.34, "abc"};

  char buf[showMaxLen(thing) + 7];
  size_t len = buildStr(buf, show(thing) + " " + (str("!") * 3) + " " + str(42) + " " + showWith(showAsInt, thing.y));
  printf("%zu\n", len);
  printf("%s\n", buf);

  if (len != strlen(buf))
    return 1;

  if (strcmp(buf, "{.x = 1, .y = 2.34, .z = \"abc\"} !!! 42 2"))
    return 2;
}
