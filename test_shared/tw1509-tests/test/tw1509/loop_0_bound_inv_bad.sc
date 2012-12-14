// Tests that loop head invariant assertions checked even with no loop unwinds
void main()
{
	int i;
	i=3;
	while(i > 2)
	bound(0)
	inv(i >= 0)
	inv(i <= 2)
	{
		i = i + 1;
	}
}

