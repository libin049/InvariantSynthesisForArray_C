int main( int src[] , int dst[] , int EOF ) {
  int i = 0; 
  while ( src[i] != EOF ) {
    dst[i] = src[i];
    i = i + 1;
  }
  
  i = 0;
  while ( src[i] != EOF ) {
    //assert( dst[i] == src[i] );
    i = i + 1;
  }
}

