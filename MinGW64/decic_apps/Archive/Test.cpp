// To compile on mingw:
//   /usr/bin/x86_64-w64-mingw32-g++ -I/usr/x86_64-w64-mingw32/sys-root/mingw/include -o Test.exe Test.cpp
// To compile on linux:
//   g++ -o Test Test.cpp



#include <stdio.h>

int main(int argc, char **argv)
  {
  //printf("Size of void    = %d.\n",sizeof(void));
  printf("Size of int     = %d.\n",sizeof(int));
  printf("Size of uint    = %d.\n",sizeof(unsigned int));
  printf("Size of char    = %d.\n",sizeof(char));
  printf("Size of uchar   = %d.\n",sizeof(unsigned char));
  //printf("Size of size_t  = %d.\n",sizeof(size_t));
  printf("Size of long    = %d.\n",sizeof(long));
  printf("Size of Long*   = %d.\n",sizeof(long*));
  printf("Size of Long**  = %d.\n",sizeof(long**));
  printf("Size of Long*** = %d.\n",sizeof(long***));
  //printf(stderr,"Size of GEN     = %d.\n",sizeof(GEN));
  //printf(stderr,"Size of pari_sp = %d.\n",sizeof(pari_sp));
  printf("Size of LongLong= %d.\n",sizeof(long long));

  return 0;
  }

