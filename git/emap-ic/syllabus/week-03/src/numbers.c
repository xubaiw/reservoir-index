#include <cs50.h>
#include <stdio.h>

int main(void)
{
    const int SIZE = 20;
    int numbers[] = {4, 6, 8, 2, 7, 5, 10, 0};

    // Search for 0
    for (int i = 0; i < SIZE; i++)
    {
        if (numbers[i] == 3)
        {
            printf("Found\n");
            return 0;
        }
    }
    printf("Not found\n");
    return 1;
}
