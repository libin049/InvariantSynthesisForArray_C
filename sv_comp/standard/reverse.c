#define N 100

int main(  ) {
	int a[N] ; int b[N];
  int i;
  for( i = 0 ; i < N ; i++ ) {
    b[i] = a[N-i-1];
  }
  //assert( forall ( int x ) :: ( 0 <= x && x < N ) ==> ( a[x] == b[N-x-1] ) );
}
