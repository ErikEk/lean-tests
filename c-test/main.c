#include <stdio.h>

/*
 * Returns the absolute value of x.
 */
int abs(int x) {
    if (x < 0)
        return -x;
    return x;
}

int main(void) {
    int values[] = { -10, -1, 0, 1, 42 };
    int n = sizeof(values) / sizeof(values[0]);

    printf("Testing abs():\n");

    for (int i = 0; i < n; i++) {
        printf("abs(%d) = %d\n", values[i], abs(values[i]));
    }

    return 0;
}
