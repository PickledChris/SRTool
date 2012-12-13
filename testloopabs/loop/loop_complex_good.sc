void main()
{
	int i;
	int n;
	int i1;
	int n1;
	
	assume(n >= 0 && n <= 10 && i >= 0 && i < 10);
	
	i1 = i;
	n1 = n;
	
	while(n1 != 0)
	inv(n1 <= n && n1 >= 0)
	inv(i1 == (i << (n-n1)))
	{
		i1 = 2*i1;
		n1 = n1-1;
	}
	
	assert(i1 == (i << n));
}


