#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
// #include <time.h>
#ifdef WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#endif
#include "verifier.c"

#define ERR_ARGS 1
#define ERR_READ 2
#define ERR_MMAP 3

int main(int argc, char** argv) {
  if (sizeof(cmd32) != 5) {
    fprintf(stderr, "Static assert: __attribute__((packed)) fail\n");
    return 999;
  }

  if (argc < 2) {
    fprintf(stderr, "Incorrect args; use 'mm0-c MMB-FILE < MM0-FILE'\n");
    return ERR_ARGS;
  }

  char* fname = argv[1];
  int fd = open(fname, O_RDONLY);
  struct stat buf;
  if (fd < 0 || fstat(fd, &buf) < 0) {
    fprintf(stderr, "Error: Unable to read file %s\n", fname);
    return ERR_READ;
  }

  size_t len = (size_t)buf.st_size;
#ifdef WIN32
  HANDLE hmap = CreateFileMapping((HANDLE)_get_osfhandle(fd), 0, PAGE_WRITECOPY, 0, 0, 0);
  if (!hmap) {
    fprintf(stderr, "Error: Unable to memory map file\n");
    return ERR_MMAP;
  }

  u8* result = (u8*)MapViewOfFileEx(hmap, FILE_MAP_COPY, 0, 0, len, 0);
  if (!result) {
    fprintf(stderr, "Error: Unable to memory map file\n");
    return ERR_MMAP;
  }

  if (!CloseHandle(hmap)) {
    fprintf(stderr, "unable to close file mapping handle\n");
    return ERR_MMAP;
  }
#else
  u8* result = (u8*) mmap(0, len, PROT_READ, MAP_FILE | MAP_PRIVATE, fd, 0);
  if (result == MAP_FAILED) {
    fprintf(stderr, "Error: Unable to memory map file\n");
    return ERR_MMAP;
  }
#endif

  // struct timespec start_time;
  // clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start_time);
  verify(len, result);
  // struct timespec end_time;
  // clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end_time);
  // long diffInNanos = (end_time.tv_sec - start_time.tv_sec) * (long)1e9 + (end_time.tv_nsec - start_time.tv_nsec);
  // printf("%ld", diffInNanos);
  return 0;
}
