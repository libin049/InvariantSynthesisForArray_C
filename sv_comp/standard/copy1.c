#define N 100

int main() {
	 int a1[N]; 
  int a2[N];
  
  int i; 
  for ( i = 0 ; i < N ; i++ ) {
    a2[i] = a1[i];
  }
  
  //assert( forall (int x) :: (0 <= x && x < N) ==> (a1[x] == a2[x]) );
}

