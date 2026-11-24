/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include "basic.h"

#define TABLE_SIZE 17
#define DEFAULT UINT64_C(0)

static const unicode_data_t table[TABLE_SIZE];

uint64_t unicode_default_ignorable_lookup(uint32_t c) {
  if (c >= table[0].cmin) {
    unsigned int lo = 0;
    unsigned int hi = TABLE_SIZE;
    unsigned int i = (lo + hi)/2;
    while (i != lo) {
      if (c < table[i].cmin) hi = i;
      else lo = i;
      i = (lo + hi)/2;
    }
    if (c <= table[i].cmax) return table[i].data;
  }
  return DEFAULT;
}

static const unicode_data_t table[] = {
{UINT32_C(173),UINT32_C(173),UINT64_C(1)},
{UINT32_C(847),UINT32_C(847),UINT64_C(1)},
{UINT32_C(1564),UINT32_C(1564),UINT64_C(1)},
{UINT32_C(4447),UINT32_C(4448),UINT64_C(1)},
{UINT32_C(6068),UINT32_C(6069),UINT64_C(1)},
{UINT32_C(6155),UINT32_C(6159),UINT64_C(1)},
{UINT32_C(8203),UINT32_C(8207),UINT64_C(1)},
{UINT32_C(8234),UINT32_C(8238),UINT64_C(1)},
{UINT32_C(8288),UINT32_C(8303),UINT64_C(1)},
{UINT32_C(12644),UINT32_C(12644),UINT64_C(1)},
{UINT32_C(65024),UINT32_C(65039),UINT64_C(1)},
{UINT32_C(65279),UINT32_C(65279),UINT64_C(1)},
{UINT32_C(65440),UINT32_C(65440),UINT64_C(1)},
{UINT32_C(65520),UINT32_C(65528),UINT64_C(1)},
{UINT32_C(113824),UINT32_C(113827),UINT64_C(1)},
{UINT32_C(119155),UINT32_C(119162),UINT64_C(1)},
{UINT32_C(917504),UINT32_C(921599),UINT64_C(1)},
};
