/* Intel XED probe for x86_coverage.py; decodes in 64-bit mode for a
   Sapphire Rapids chip.

     xed_probe iforms   print "IFORM ICLASS ISA_SET" for every iform
     xed_probe decode   for each line of hex bytes, print "LEN IFORM", or
                        "- ERROR" when XED rejects the bytes
     xed_probe sweep    for line i, "HEAD TAIL" in hex, print "i B LEN IFORM"
                        for each byte B such that HEAD B TAIL (cut to 15
                        bytes) is valid, LEN being its length */
#include <stdio.h>
#include <string.h>
#include "xed/xed-interface.h"

static int hex_digit(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

/* Reads up to 15 bytes of lower-case hex from *text, advancing it. */
static unsigned parse_hex(const char **text, unsigned char *out) {
  unsigned n = 0;
  while (n < 15 && hex_digit((*text)[0]) >= 0 && hex_digit((*text)[1]) >= 0) {
    out[n++] = (unsigned char)(hex_digit((*text)[0]) * 16 + hex_digit((*text)[1]));
    *text += 2;
  }
  return n;
}

static xed_error_enum_t decode(xed_decoded_inst_t *d, const unsigned char *bytes, unsigned n) {
  xed_decoded_inst_zero(d);
  xed_decoded_inst_set_mode(d, XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b);
  xed_decoded_inst_set_input_chip(d, XED_CHIP_SAPPHIRE_RAPIDS);
  return xed_decode(d, bytes, n);
}

static const char *iform_name(const xed_decoded_inst_t *d) {
  return xed_iform_enum_t2str(xed_decoded_inst_get_iform_enum(d));
}

int main(int argc, char **argv) {
  const char *mode = argc > 1 ? argv[1] : "";
  xed_tables_init();
  if (strcmp(mode, "iforms") == 0) {
    for (int i = 1; i < XED_IFORM_LAST; i++) {
      xed_iform_enum_t f = (xed_iform_enum_t)i;
      printf("%s %s %s %s\n", xed_iform_enum_t2str(f),
             xed_iclass_enum_t2str(xed_iform_to_iclass(f)),
             xed_isa_set_enum_t2str(xed_iform_to_isa_set(f)),
             xed_category_enum_t2str(xed_iform_to_category(f)));
    }
    return 0;
  }
  if (strcmp(mode, "decode") != 0 && strcmp(mode, "sweep") != 0) {
    fprintf(stderr, "usage: xed_probe iforms|decode|sweep\n");
    return 2;
  }
  char line[128];
  xed_decoded_inst_t d;
  for (unsigned long i = 0; fgets(line, sizeof line, stdin); i++) {
    const char *p = line;
    unsigned char head[15], tail[15], word[31];
    unsigned h = parse_hex(&p, head);
    if (mode[0] == 'd') {
      xed_error_enum_t e = decode(&d, head, h);
      if (e == XED_ERROR_NONE)
        printf("%u %s\n", xed_decoded_inst_get_length(&d), iform_name(&d));
      else
        printf("- %s\n", xed_error_enum_t2str(e));
      continue;
    }
    p += strspn(p, " ");
    unsigned t = parse_hex(&p, tail);
    memcpy(word, head, h);
    memcpy(word + h + 1, tail, t);
    unsigned n = h + 1 + t < 15 ? h + 1 + t : 15;
    for (int b = 0; b < 256; b++) {
      word[h] = (unsigned char)b;
      if (decode(&d, word, n) == XED_ERROR_NONE)
        printf("%lu %02x %u %s\n", i, b, xed_decoded_inst_get_length(&d), iform_name(&d));
    }
  }
  return 0;
}
