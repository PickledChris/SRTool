void main(int a, int b)
{
    int a0;
    a0= a;
    int b0;
    b0= b;

    a = a^b;
    b = a^b;
    a = a^b;

    assert(a0 == b && a == b0);
}
