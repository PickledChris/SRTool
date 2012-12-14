void main() {
  int i;
  int j;

  i = 1;
  j = 0;

  while (i) {
    i = 0;
    j = 1;
  }
  
  assert(!i);
  assert(j);
}
