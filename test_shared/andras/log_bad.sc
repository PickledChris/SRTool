void main(int a)
{
    assume (a > 9000);
    assume (a < 100000);

    int x;
    x = a;
    int l;
    l = 0;

    while (x > 1)
    bound(31)
    {
        l = l + 1;
        x = x >> 1;
    }


    /* l = log2 (a) */

    int m;
    m = 1;
    while (l != 0)
    bound(31)
    {
        m = 2 * m;
        l = l - 1;
    }
    
    assert (a < m);
}
