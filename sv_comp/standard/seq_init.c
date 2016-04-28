#define SIZE 100

int main( ) {
	int a[ SIZE ] ;
  int i;
  i = 1;
  a[0] = 7;
  while( i < SIZE ) {
    a[i] = a[i-1] + 1;
  }

  //assert( forall (int x) :: ( 0 <= x && x < SIZE ) ==> (a[x] <= a[x-1]));
}
