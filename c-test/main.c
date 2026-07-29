// gcc -o c-test/main c-test/main.c
#include <stdio.h>
#include <math.h>
/*
 * Returns the absolute value of x.
 */
int abs(int x) {
    if (x < 0)
        return -x;
    return x;
}
int square(int x) {
    return x*x;
}
// Computes base^exp for non-negative integer exponents
long long power(int base, int exp) {
    long long result = 1;
    long long b = base;

    while (exp > 0) {
        // If exp is odd, multiply b with result
        if (exp % 2 == 1) {
            result *= b;
        }
        // exp must be even now
        b *= b; // Square the base
        exp /= 2; // Divide exponent by 2
    }

    return result;
}

int main(void) {
    int values[] = { -10, -1, 0, 1, 42 };
    int n = sizeof(values) / sizeof(values[0]);
    
    int n_square = square(5);
    
    printf("square of 5 is %d\n", n_square);

    printf("Testing abs():\n");

    for (int i = 0; i < n; i++) {
        printf("abs(%d) = %d\n", values[i], abs(values[i]));
    }
    int n_large_1 = power(2,20);
    int n_large_2 = power(2,32);
    printf("overflow: %d %d\n", n_large_1, n_large_2);
    return 0;
}
