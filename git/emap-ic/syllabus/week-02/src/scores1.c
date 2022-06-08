#include <cs50.h>
#include <stdio.h>

int main(void)
{
    int n = get_int("Quantidade de números: ");
    int scores[n];

    int sum = 0;

    for(int i = 0; i < n; i++)
    {
        scores[i] = get_int("score: ");
        sum = sum + scores[i];
    }

    printf("Os numeros recebidos são: ");
    for(int i = 0; i < n; i++)
    {
        printf("%i ", scores[i]);
    }
    printf("\n");

    printf("Average: %f\n", sum / (float) n);
}

