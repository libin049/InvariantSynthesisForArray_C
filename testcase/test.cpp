
//
//int main() {
//  int N;
//  int a[N] ;
//  bool swapped = true;
//  while ( swapped==true ) {
//    swapped = false;
//    int i = 1;
//    while ( i < N ) {
//      if ( a[i - 1] > a[i] ) {
//        int t = a[i];
//        a[i] = a[i - 1];
//        a[i-1] = t;
//        swapped = true;
//      }
//      i = i + 1;
//    }
//  }
//  //assert( forall ( int x, int y ) :: ( 0 <= x && x < y && y < N ) ==> ( a[x] <= a[y] ) );
//}







//#define MAXSIZE 100
//int main( ) {
//    int array[MAXSIZE];
//    int i;
//    int num;
//    int negative_sum;
//    int positive_sum;
//    
//    negative_sum = 0;
//    positive_sum = 0;
//
//    /*  Summation starts */
//    for (i = 0; i < MAXSIZE; i++)
//    {
//        if (array[i] < 0)
//        {
//            negative_sum = negative_sum + array[i];
//        }
//        else
//        {
//            positive_sum = positive_sum + array[i];
//        }
//        
//    }
//    //assert( negative_sum <= 0 );
//    //assert( positive_sum >= 0 );
//    //assert( forall (int x) :: (0 <= x && x < MAXSIZE) ==> ( array[x] <= positive_sum ) );
//    //assert( forall (int x) :: (0 <= x && x < MAXSIZE) ==> ( array[x] >= negative_sum ) );
//}


//
//char *strcpy(char dest[], char src[],char tmp[])
// {
//         tmp=dest;
//		  int desti=0;
//		  int srci=0;
//         if ((desti==0&&srci==0)||(desti==1&&srci==1)){
//			return src;
//		A highly expressive and flexible approach }
//                 /* nothing */;
//         return tmp;
// }

//int strcmp()
// {
//	 
//		  const char *cs;
//		  const char *ct;
//         unsigned char c1, c2;
// 
//         while (1) {
//                 c1 = *cs;
//                 c2 = *ct;
//                 if (c1 != c2)
//                         return -1;
//                 if (!c1)
//                         break;
//				   cs++;
//				   ct++;
//         }
//         return 0;
// }
 
 char *strncpy()
 {
		char *dest; const char *src; int count=100;
         char *tmp = dest;
 
         while (count) {
                 if ((*tmp = *src) != 0)
                         src++;
                 tmp++;
                 count--;
         }
         return dest;
 }
//  void strncpy()
// {
//		int count;
//		char dest[count]; char src[count]; 
//		int dest_index=0;
//		int src_index=0; 
//		char tmp = dest[dest_index];
//			
//         while (count) {
//                 if ((tmp = src[src_index]) != 0)
//                         src_index++;
//                 tmp = dest[dest_index];
//				   dest_index++;
//                 count--;
//         }
//         
// }

//void strncpy(){
//int dest_index=0;
//int i7_2=0; 
//int src_index=0; 
//int count=100; 
////tmp_initbase=dest_initbase; 
//int tmp_index=dest_index; 
//char dest_initbase[count]; 
//char src_initbase[count];
//src_initbase=dest_initbase; 
//while(count){
//	dest_initbase[i7_2+dest_index]= src_initbase[src_index]; 
// 	if(src_initbase[src_index]!=0){
//		src_index++;
//	} 
//	tmp_index=i7_2+dest_index+1; 
//	count=count-1; 
//	i7_2=i7_2+1; 
//}
//}

/*int strncmp(const char *cs, const char *ct,int count_init)
{
         unsigned char c1, c2;
 	 int count=count_init;
	 int cs_index=0;
	 int ct_index=0; 
         while (count) {
                c1 = cs[cs_index];
				  
                c2 = ct[ct_index];
				  
                 if (c1 != c2){
                         if(c1 < c2) return -1 ;
							else return 1;
					}
                 if (!c1)
                         break;
               cs_index++;
			    ct_index++;  
				 count--;
         }
         return 0;
}*/
//char *strcpy(char *dest, const char *src)
// {
//          char *tmp = dest;
//			do{
//				dest[dest_index] = src[src_index];
//				dest_index++;
//				src_index++;
//			}
//          while (src[src_index]!= '\0')
//                  /* nothing */;
//          return tmp;
//  }
/*int strncmp(const char *cs, const char *ct,int count_init)
{
	 unsigned char c1, c2;
 	 int count=count_init;
	 int cs_index=0;
	 int ct_index=0; 
	 while (count) {
		cs_index++;
		ct_index++;
		count--;
	 }
         return 0;
}*/
