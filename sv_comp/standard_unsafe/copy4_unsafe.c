#define N 100

int main() {
	 int a1[N]; 
  int a2[N];
  int a3[N];
  int a4[N];
  int a5[N];
  
  int i; 
  for ( i = 0 ; i < N ; i++ ) {
    a2[i] = a1[i];
  }
  for ( i = 0 ; i < N ; i++ ) {
    a3[i] = a2[i];
  }
  for ( i = 0 ; i < N ; i++ ) {
    a5[i] = a3[i];
  }
  for ( i = 0 ; i < N ; i++ ) {
    a5[i] = a4[i];
  }
  
  //assert( forall (int x) :: (0 <= x && x < N) ==> (a1[x] == a5[x]) );
}

