void main() {
  int i;
  int j;

  i = 1;
  j = 0;

  if (i) {
    if (j) {}
    j = 1;
  }

  assert (i);
  assert (j);
}
