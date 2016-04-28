#define N 100

int main () {
	 int A[ N ] ; int B[ N ] ; int C[ N ] ;
  int i;
  int j = 0;
  for (i = 0; i < N ; i++) {
    if ( A[i] == B[i] ) {
      C[j] = i;
      j = j + 1;
    }
  }

  //assert( forall ( int x ) :: ( 0 <= x && x < j ) ==> ( C[x] <= x + i - j ) );
  //assert( forall ( int x ) :: ( 0 <= x && x < j ) ==> ( C[x] >= x ) );
}
