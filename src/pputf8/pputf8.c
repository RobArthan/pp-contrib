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

enum {	S_INITIAL,
	S_HAVE_PERCENT,
	S_HAVE_X,
	S_HAVE_HEXIT_1,
	S_HAVE_HEXIT_2,
	S_HAVE_HEXIT_3,
	S_HAVE_HEXIT_4,
	S_HAVE_HEXIT_5,
	S_HAVE_HEXIT_6,
	S_HAVE_KEYWORD};

typedef char bool;

enum {False = 0, True = 1};

static bool is_uc_hexit(char ch)
{
	return ('0' <= ch && ch <= '9') || ('A' <= ch && ch <= 'F');
}

static bool is_percent(char ch)
{
	return ch == '%';
}

static bool is_x(char ch)
{
	return ch == 'x';
}

static void do_chars(int len, char *cs)
{
	while(len--) {
		printf("%s", pp_to_utf8[(int)*cs++ & 0xff]);
	}
}

static bool do_keyword(unsigned u)
{
	if(u <= 0x7f) { /* <= 7 bits */
		return False;
	} else if (u <= 0x7ff) { /* <= 11 bits */
		putchar(0xc0u | (u >> 6u));
		putchar(0x80u | (u & 0x3fu));
		return True;
	} else if (u <= 0xffff) { /* <= 16 bits */
		putchar(0xe0u | (u >> 12u));
		putchar(0x80u | ((u & 0xfc0u) >> 6u));
		putchar(0x80u | (u & 0x3fu));
		return True;
	} else if (u <= 0x10ffffu) { /* <= max code point, so <= 21 bits */
		putchar(0xf0u | (u >> 18u));
		putchar(0x80u | ((u & 0x3f000u) >> 12u));
		putchar(0x80u | ((u & 0xfc0u) >> 6u));
		putchar(0x80u | (u & 0x3fu));
		return True;
	} else {
		return False;
	}
}

#define STEP(TST, ST) \
	if((TST)(whatgot)) {\
		state = (ST);\
	} else {\
		do_chars(l, buf);\
		l = 0;\
		state = S_INITIAL;\
	};\
	break;

static void do_pp_to_utf8 (void)
{
	int whatgot, state, l;
	char buf[9];
	unsigned u;
	l = 0;
	state = S_INITIAL;
	while ((whatgot = getchar()) != EOF) {
		buf[l++] = whatgot;
		switch(state) {
			case S_INITIAL:      STEP(is_percent,  S_HAVE_PERCENT);
			case S_HAVE_PERCENT: STEP(is_x,              S_HAVE_X);
			case S_HAVE_X:       STEP(is_uc_hexit, S_HAVE_HEXIT_1);
			case S_HAVE_HEXIT_1: STEP(is_uc_hexit, S_HAVE_HEXIT_2);
			case S_HAVE_HEXIT_2: STEP(is_uc_hexit, S_HAVE_HEXIT_3);
			case S_HAVE_HEXIT_3: STEP(is_uc_hexit, S_HAVE_HEXIT_4);
			case S_HAVE_HEXIT_4: STEP(is_uc_hexit, S_HAVE_HEXIT_5);
			case S_HAVE_HEXIT_5: STEP(is_uc_hexit, S_HAVE_HEXIT_6);
			case S_HAVE_HEXIT_6: STEP(is_percent,  S_HAVE_KEYWORD);
		}
		if(state == S_HAVE_KEYWORD) {
			sscanf(&buf[2], "%6X", &u);
			if(!do_keyword(u)) { do_chars(l, buf); }
			l = 0;
			state = S_INITIAL;
		}
	}
}

static void usage(void)
{
	printf("pputf8"
		": convert ProofPower extended character format to UTF-8\n");
	printf("usage: pputf8 < input_file > output_file\n");
}

int main (int argc, char *argv[])
{
	if(argc == 1) {
		do_pp_to_utf8();
		return ferror(stdin) || ferror(stdout);
	} else {
		usage();
		return 0;
	}
}
