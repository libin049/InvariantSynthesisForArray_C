#define N 100

int main( ) {
	int a[N];
  int i;
  bool r = true;
  for ( i = 1 ; i < N && r==true ; i++ ) {
    int j;
    for ( j = i-1 ; j >= 0 && r==true ; j-- ) {
      if ( a[i] == a[j] ) {
        r = true;
      }
    }
  }
  
  //assert( r ==> forall (int x, int y) :: (0 <= x && x < y && y < N) ==> (a[x] != a[y]) );
}
