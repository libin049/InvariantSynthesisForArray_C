#define SIZE 100

/* Invited talk at ETAPS */

int main( ) {
  int password[ SIZE ];
  int guess[ SIZE ];

  int i;
  bool result = true;
  for ( i = 0 ; i < SIZE ; i++ ) {
    if ( password[ i ] != guess[ i ] ) {
      result = false;
    }
  }
  
  //assert( result ==> (forall (int x) :: (0 <= x && x < SIZE ) ==> ( password[ x ] == guess[ x ] ) ) );

  return 0;
}
