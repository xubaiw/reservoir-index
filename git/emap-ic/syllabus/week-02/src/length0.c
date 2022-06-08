
#include <cs50.h>
#include <stdio.h>

int main(int argc, string argv[])
{
    // Count number of characters up until '\0' (aka NUL)
    int n = 0;
    string name = argv[1];

    while (name[n] != '\0')
    {
        n++;
    }
    printf("%i\n", n);
}
