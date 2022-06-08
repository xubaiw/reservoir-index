// Prints a command-line argument

#include <cs50.h>
#include <stdio.h>

int main(int argc, string argv[])
{
    if (argc == 2)
    {
        printf("Eu %s recebi um nome! hello, %s\n", argv[0], argv[1]);
    }
    else
    {
        printf("hello, world\n");
    }
}
