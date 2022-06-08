#include <cs50.h>
#include <stdio.h>

/* 
 author: Alexandre Rademaker

 - return value, multiple arguments
 - test user input
*/

float discount(float price, int percentage);

int main(void)
{
    float regular_price = get_float("Regular Price: ");
    int percent_off;
    do
    {
	    percent_off = get_int("Percent Off: ");
    } while (percent_off < 0 || percent_off > 100);

    printf("Sale Price: %.2f\n", discount(regular_price, percent_off));
}


float discount(float price, int percentage)
{
    return price * (100 - percentage) / 100;
}
