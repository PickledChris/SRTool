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
  // We cannot assert j, as no invariants, this is mostly a test that the
  // analyser can handle loops with no invariants
}
