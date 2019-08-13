#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <stdio.h>
#include <stdlib.h>
#include "verifier.c"

#define ERR_ARGS 1
#define ERR_READ 2
#define ERR_MMAP 3

int main(int argc, char** argv) {
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
  u8* result = (u8*) mmap(0, len, PROT_READ, MAP_FILE | MAP_PRIVATE, fd, 0);
  if (result == MAP_FAILED) {
    fprintf(stderr, "Error: Unable to memory map file\n");
    return ERR_MMAP;
  }

  verify(len, result);
  return 0;
}
