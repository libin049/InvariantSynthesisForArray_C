#define N 100

int main() {
	 int a[N] ;
  int i;
  for ( i = 0 ; i < N ; i++ ) {
    a[i] = i;
  }
  
  //assert( forall (int x) :: (0 <= x && x < N) ==> (a[x] == x) );
}
