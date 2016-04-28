#define SIZE 100

int main() {
	int a [SIZE] ; 
	int b [SIZE] ;
  int i = 0;
  int c [SIZE];
  bool rv = true;
  while ( i < SIZE ) {
    if ( a[i] != b[i] ) {
      rv = false;
    }
    c[i] = a[i];
    i = i+1;
  }
  //assert( rv ==> (forall (int x) :: (x >= 0 && x < SIZE) ==> (a[x] == b[x])));
  //assert( forall (int x) :: (x >= 0 && x < SIZE) ==> (a[x] == c[x]));
}
