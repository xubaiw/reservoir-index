#include <stdio.h>
#include <cs50.h>

int main(void)
{
    string ans1 = get_string("qual seu nome? ");
    int ans2 = get_int("qual sua idade? ");
    int year = 2022;

    printf("hello, %s você tem %i em %i!\n", ans1, ans2, year);
}
