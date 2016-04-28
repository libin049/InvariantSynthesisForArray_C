#define N 100

int main() {
	 int a[N] ;
  bool swapped = true;
  while ( swapped==true ) {
    swapped = false;
    int i = 1;
    while ( i < N ) {
      if ( a[i - 1] > a[i] ) {
        int t = a[i];
        a[i] = a[i - 1];
        a[i-1] = t;
        swapped = true;
      }
      i = i + 1;
    }
  }
  //assert( forall ( int x, int y ) :: ( 0 <= x && x < y && y < N ) ==> ( a[x] <= a[y] ) );
}
