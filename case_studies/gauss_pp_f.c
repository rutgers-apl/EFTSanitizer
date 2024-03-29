#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define N 4


void swap(float *x, float *y)
{
  float tmp = *x;
  *x = *y;
  *y = tmp;
}

void MatrixSolve()
{
  int i, j, k;
  float A[N][N] = {
    {21.0f, 130.0f, 0.0f, 2.1f},
    {13.0f, 80.0f, 4.74E+8f, 752.0f},
    {0.0f, -0.4f, 3.9816E+8f, 4.2f},
    {0.0f, 0.0f, 1.7f, 9E-9f}
  };
  float b[N] = {
    153.1f,
    849.74f,
    7.7816,
    2.6E-8f
  };
  float x[N];
  float U[N][N+1];

  // Copy A to U and augment with vector b.
  for (i = 0; i < N; i++)
  {
    U[i][N] = b[i];
    for (j = 0; j < N; j++)
      U[i][j] = A[i][j];
  }

  // Factorisation stage
  for (k = 0; k < N; k++)
  {
    // Find the best pivot
    int p = k;
    float maxPivot = 0.0;
    for (i = k; i < N; i++)
    {
      if (fabs(U[i][k] > maxPivot))
      {
        maxPivot = fabs(U[i][k]);
        p = i;
      }
    }

    // Swap rows k and p
    if (p != k)
    {
      for (i = k; i < N + 1; i++)
        swap(&U[p][i], &U[k][i]);
    }

    // Elimination of variables
    for (i = k + 1; i < N; i++)
    {
      float m = U[i][k] / U[k][k];
      for (j = k; j < N + 1; j++){
        U[i][j] -= m * U[k][j];
      }
    }
  }
  // Back substitution
  for (int k = N - 1; k >= 0; k--)
  {
    float sum = U[k][N];
    for (int j = k + 1; j < N; j++){
      float t = U[k][j] * x[j];
      sum -= t;
    }
    x[k] = sum / U[k][k];
  }
  for (int i=0; i<N; i++){
    printf("%.9g\n", x[i]);
  }
}

int main(){
  MatrixSolve();
}
