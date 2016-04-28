#define N 100

int main () {
	 int a [N] ;
  int i = 0;
  while ( i < N ) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 43;
    i = i + 1;
  }

  //assert( forall (int x) :: (0 <= x && x < N) ==> ( a[x] == 43 ) );
}
