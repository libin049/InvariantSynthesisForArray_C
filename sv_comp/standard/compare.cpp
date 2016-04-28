#define SIZE 100

int main() {
	int a [SIZE] ; 
	int b [SIZE] ;
  int i = 0;
  bool rv = true;
  while ( i < SIZE ) {
    if ( a[i] != b[i] ) {
      rv = false;
    }
    i = i+1;
  }
  //assert( rv ==> (forall (int x) :: (x >= 0 && x < SIZE) ==> (a[x] == b[x])));
}
