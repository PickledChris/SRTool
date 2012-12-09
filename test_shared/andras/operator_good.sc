void main()
{
    int a;
    a = 11;
    int b;
    b = 24;
    int c;

    c = a + b;
    assert(c==35);

    c = a & b;
    assert(c==8);

    c = a | b;
    assert(c==27);

    c = a ^ b;
    assert(c==19);

    c = a | b;
    assert(c==27);

    c = b / a;
    assert(c==2);

    c = a << 2;
    assert(c==44);

    c = b % a;
    assert(c==2);

    c = a * b;
    assert(c==264);

    c = a >> 2;
    assert(c == 2);

    c = a - b;
    assert(c==-13);

    c = a >= b;
    assert(c==0);

    c = a > b;
    assert(c==0);

    c = a <= b;
    assert(c==1);

    c = a < b;
    assert(c==1);

    c = a != b;
    assert(c==1);

    c = a == b;
    assert(c==0);

    c = a && b;
    assert(c);

    c = a || b;
    assert(c);
}
