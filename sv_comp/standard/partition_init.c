#define N 100

int main(){
	 int aa[N] ; int cc[N] ;
  int bb [N];
  int a = 0;
  int b = 0;
  while( a < N ) {
    if( aa[a] == cc[a] ) {
      bb[b] = a;
      b = b + 1;
    }
    a = a + 1;
  }

  //assert( forall (int x, int y) :: ( 0 <= x && x < b && y == bb[x] ) ==> ( aa[y] == cc[y]) );
}

