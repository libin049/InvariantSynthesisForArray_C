#define N 100

int main() {
	 int a[N] ;
  int max = 0;
  int i = 0;
  while ( i < N ) {
    if ( a[i] > max ) {
      max = a[i];
    }
    i = i + 1;
  }
  //assert( forall (int x) :: (0 <= x && x < N) ==> a[x] <= max );
}
