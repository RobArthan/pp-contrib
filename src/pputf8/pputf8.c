/*
 * pputf8.c: convert from the ProofPower extended character set to utf-8
 *
 * Rob Arthan rda@lemma-one.com
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
/*
 * The include file pputf8tab.h is automatically generated from some ML
 * code. It contains an array pp_to_utf8 containing 256 strings.
 * Conversion from the ProofPower extended character set to utf-8
 * is just a look-up in this array.
 * Note that a few characters map to string of more than one unicode
 * characters.
 */
#include "pputf8tab.h"


static void do_pp_to_utf8 (void)
{
	int whatgot;
	while ((whatgot = getchar()) != EOF) {
		printf("%s", pp_to_utf8[whatgot]);
	}
}


int main (int argc, char *argv[])
{
	do_pp_to_utf8();
	return ferror(stdin) || ferror(stdout);
}
