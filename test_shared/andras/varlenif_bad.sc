// An example where the number of assignments to parent-scoped
// variables varies.
//
// In other words: In the inner if blocks, we have more or
// fewer z=something.
//
// This can break simple SSA.

void main(int c, int d)
{
  int z;

  z=0;

  if(c)
  {
    z=1;
    if(d)
    {
      z=10;
      z=2;
    }
    else
    {
      z=3;
    }
  }
  else
  {
    z=5;
    z=6;
    z=7;
    z=8;
  }

  z=9;

  assert(0);
}
