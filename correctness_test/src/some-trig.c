#include <stdio.h>
#include <math.h>
extern void eftsan_print_error(double);
int main() {
  double x, y;
  x = atan(1.0) * (40002);
  y = tan(x) - (sin(x)/cos(x));
  printf("%e\n", y);
  eftsan_print_error(y);
  return 0;
}
