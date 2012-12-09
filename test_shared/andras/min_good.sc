void main(int a, int b)
{

    int c;
    if (a <= b)
    {
        c = a;
    }
    else
    {
        c = b;
    }

    assert (c <= b && c <= a);
}
