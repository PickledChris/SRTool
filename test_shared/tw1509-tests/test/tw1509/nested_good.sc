void main() {
  int i;
  int j;
  int k;
  i = 0;
  k = 0;

  while (i < 2) {
    i = i + 1;
    j = 0;
    while (j < 2) {
      j = j + 1;
      k = k + 1;
    }
  }

  assert (i == 2);
  assert (j == 2);
  assert (k == 4);
    
}
