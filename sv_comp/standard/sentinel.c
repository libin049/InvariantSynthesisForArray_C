#define N 100

int main () {
	 int a[N] ; int marker ;
  int pos;
  //assume( pos >= 0 );
  //assume( pos < N );

  a[ pos ] = marker;

  int i = 0;
  while( a[ i ] != marker ) {
    i = i + 1;
  }
 
  // should infer that ( forall x :: ( 0 <= x < i ) ==> ( a[ x ] != marker ) )
  
  //assert( i <= pos );
}
