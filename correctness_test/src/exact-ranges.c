#include <stdio.h>
#include <math.h>
extern void eftsan_print_error(double);
double inputs[12] = {
  0.7745966692414830, 0.7745966692414831, 0.7745966692414832, 0.7745966692414833,
  0.7745966692414834, 0.7745966692414835, 0.7745966692414836, 0.7745966692414837,
  0.7745966692414838, 0.7745966692414840, 0.7745966692414841, 0.7745966692414842
};

int main() {
  volatile double x, y;
  for (int i = 0; i < 12; i++) {
    x = inputs[i];
    y = 5.0*x*x - 3.0;
    eftsan_print_error(y);
    printf("%e\n", y);
  }
  return 0;
  
}

