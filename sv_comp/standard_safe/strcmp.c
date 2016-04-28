#define N 100

int strcmp() {
	 int src[N] ; int dst[N]; 
  int i = 0; 
  while ( i < N ) {
    if( dst[i] != src[i] ) return 1;
    i = i + 1;
  }
  return 0;
}


int main( ) {
  int a[N];
  int b[N];
  
  int c = strcmp( a , b );

  //assert( c == 0 ==> (forall (int x) :: (0 <= x && x < N) ==> (a[x] == b[x]) ) );
}
