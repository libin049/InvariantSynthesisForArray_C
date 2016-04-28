#define N 100

int main( ) {
	int aa[N] ;
  int a = 0;
  int b = 0;
  int c = 0;
  int bb[N];
  int cc[N];
  
  while( a < N ) {
    if( aa[ a ] >= 0 ) {
      bb[ b ] = aa[ a ];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  while( a < N ) {
    if( aa[ a ] >= 0 ) {
      cc[ c ] = aa[ a ];
      c = c + 1;
    }
    a = a + 1;
  }
  //assert( forall (int x) :: (0 <= x && x < b) ==> ( bb[ x ] >= 0 ) );
  //assert( forall (int x) :: (0 <= x && x < c) ==> ( cc[ x ] < 0 ) );
}


