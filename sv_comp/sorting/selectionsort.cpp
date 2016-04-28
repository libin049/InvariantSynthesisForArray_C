#define N 100

int main() {
	 int a[N] ;
  int i = 0;
  while ( i < N ) {
    int k = i + 1;
    int s = i;
    while ( k < N ) {
      if ( a[k] < a[s] ) {
        s = k;
      }
      k = k+1;
    }
    if ( s != i ) {
      int tmp = a[s];
      a[s] = a[i];
      a[i] = tmp;
    }
    
    //assert( forall ( int x, int y ) :: ( 0 <= x && x < y && y < i ) ==> ( a[x] <= a[y] ) );
    //assert( forall ( int x ) :: ( i < x && x < N ) ==> ( a[x] >= a[i] ) );
    
    i = i+1;
  }
    
  //assert( forall ( int x, int y ) :: ( 0 <= x && x < y && y < N ) ==> ( a[x] <= a[y] ) );
}
