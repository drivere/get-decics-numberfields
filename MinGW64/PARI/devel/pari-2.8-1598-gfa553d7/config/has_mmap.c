#include <unistd.h>
#include <sys/mman.h>
#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif
#ifndef MAP_NORESERVE
#define MAP_NORESERVE 0
#endif
int main(void)
{
  size_t size = sysconf(_SC_PAGE_SIZE)*1000;
  void *b = mmap(NULL, size, PROT_READ|PROT_WRITE,
                             MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE,-1,0);
  madvise(b, size, MADV_DONTNEED);
  munmap(b, size);
  return 0;
}
