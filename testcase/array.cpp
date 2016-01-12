void arrayCopy(int A[],int B[],unsigned size){
	for(int i=0;i<size;i++){
		A[i]=B[i];		
	}
}

bool arrayIf(int A[],int B[],unsigned size){
	for(int i=0;i<size;i++){
		if(A[i]==0){
			return true;
		}
	}
	return false;
}

void towDarrayCopy(int** A,int** B,unsigned row,unsigned col){
	for(int i=0;i<row;i++){
		for(int j=0;j<col;j++){			
			A[i][j]=B[i][j];
		}
	}
}

bool towDarrayIf(int** A,int** B,unsigned row,unsigned col){
	bool flag=false;
	for(int i=0;i<row;i++){
		for(int j=0;j<col;j++){	
			if(A[i][j]==0){
				flag=true;
				break;
			}
		}
		if(flag==true){
			break;
		}
	}
	return flag;
}

bool towDarrayIf2(int** A,int** B,unsigned row,unsigned col){
	for(int i=0;i<row;i++){
		for(int j=0;j<col;j++){	
			if(A[i][j]==0){
				return true;
			}
		}
		
	}
	return false;
}

void arrayMax(int A[],unsigned size){      
	int max=A[0];
	for(int i=0;i<size;i++){
         if(max<A[i]){
             max=A[i];
         }
    }
}

void arrayInit(int A[],unsigned size){
	A[0]=7;
	for(int i=0;i<size;i++){
         A[i]=A[i-1]+1;
    }
}
//
void arrayInit2(int A[],unsigned size){
	A[0]=7;
	for(int i=1;i<size;i++){
         A[i-1]=A[i]+1;
    }
}
//
void arrayInit3(int A[],unsigned size){
	for(int i=0;i<size;i++){
        A[i]=0;
    }
}
//
//
 void arraySentinel(int A[],unsigned size,int x){
        int i=0;
        while(A[i]!=x&&i<size){
            i=i+1;
        }
}
void arraySentinel2(int A[],unsigned size,int x){
        A[size]=x; 
	int i=0;
        while(A[i]!=x&&i<size){
            i=i+1;
        }
  }

void arrayPartition(int A[],int B[], int C[],unsigned size,int x){
        int i=0,j=0,k=0;
        while(i<size){
            if(A[i]<x){
                B[j]=A[i];
                j++;
            }
            else{
                C[k]=A[i];
                k++;
            }
            i++;
        }
    }
void towArrayInit(int** A,unsigned row,unsigned col){
   for(int i=0;i<row;i++){
      for(int j=0;j<col;j++){
           A[i][j]=0;
       }
   }
}
//
//
 void firstNotNull(int A[],unsigned size){
        int s=size+1;;
        for(int i=0;i<size;i++){
            if(A[i]!=0){
                s=i;
		break;
            }
        }
  }

//we can not process this
void firstNotNull2(int A[],unsigned size){
        int s=size+1;
        for(int i=0;i<size;i++){
            if(s==size+1&&A[i]!=0){
                s=i;
            }
        }
  }

void threeDarrayCopy(int*** A,int*** B,unsigned d1,unsigned d2,unsigned d3){
	for(int i=0;i<d1;i++){
		for(int j=0;j<d2;j++){			
			for(int k=0;k<d3;k++){
				A[i][j][k]=B[i][j][k];
			}
		}
	}
}

void threeDarrayCheck(int*** A,int*** B,unsigned d1,unsigned d2,unsigned d3){
	for(int i=0;i<d1;i++){
		for(int j=0;j<d2;j++){			
			for(int k=0;k<d3;k++){
				if(A[i][j][k]==0){
					goto L;
				}
			}
		}
	}
	L:;
}


//part of quick sort 
    void find(int A[],unsigned size){
        int x = A[0] ;
        int i = 1;
        int j =size-1;
        while (i<=j){
            if (A[i] < x){
                A[i-1] = A[i] ;
                i = i + 1;
            }
            else{
                while(j>=i&&A[j]>=x){
                    j = j-1;
                }
                if (j > i){
                    A[i-1] = A[j];
                    A[j] = A[i];
                    i = i + 1 ;
                    j = j-1;
                }
            }
        }
        A[i-1] = x ;
    }
//
void arrayInit4(int A[],unsigned size){
	for(int i=1;i<size;i=i+2){
        A[i]=0;
    }
}

bool threeDarrayCheck2(int*** A,int*** B,unsigned d1,unsigned d2,unsigned d3){
	for(int i=0;i<d1;i++){
		for(int j=0;j<d2;j++){			
			for(int k=0;k<d3;k++){
				if(A[i][j][k]==0){
					return true;
				}
			}
		}
	}
	return false;
}

