#define N 100

int main() {
	 int A[N] ;
  int i;
  for (i = 0; i < N/2 ; i++ ) {
    A[i] = A[N-i-1];
  }
  
  //assert( forall ( int x ) :: ( 0 <= x && x < N/2 ) ==> ( A[x] == A[N - x - 1] ) ); 
}
