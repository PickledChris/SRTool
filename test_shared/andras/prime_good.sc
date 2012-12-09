/* The assertion holds if 'a' is a prime */
void main ()
{
    int a;
    a = 7;                      /* Specify the prime to be checked here */

    int x;
    x = 2;
    int t;
    t = 0;
    while (x < a && !t)
    bound(10)
    {
        t = (a % x) == 0;
        x = x + 1;
    }

    assert(!t);
}
