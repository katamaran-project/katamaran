/* PLAN-rsa.md Phase 1, spike S1: the call pattern of the last line of
 * br_i31_montymul (src/int/i31_montmul.c), verbatim, in its own function so
 * the link needs only br_i31_sub. */
#include "inner.h"

void
rsa_spike_sub2(uint32_t *d, const uint32_t *m, uint32_t dh)
{
	br_i31_sub(d, m, NEQ(dh, 0) | NOT(br_i31_sub(d, m, 0)));
}
