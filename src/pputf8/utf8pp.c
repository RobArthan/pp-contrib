/*
 * pputf8.c: convert UTF-8 to the ProofPower extended character set.
 *
 * Rob Arthan rda@lemma-one.com
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
/*
 * The include file utf8pptab.h is automatically generated from some ML
 * code. It contains an array of records each containing a Unicode code
 * point (represented as a signed int) and the corresponding ProofPower character.
 * The array is sorted by * the code point and we do the associative lookup
 * with bsearch.
 */
#include "utf8pptab.h"
int utf8pp_error = 0;
int line;

int utf8_to_pp_entry_cmp(const void *buf1, const void *buf2)
{
	const utf8_to_pp_entry *u1 = buf1, *u2 = buf2;
	return  u1->code_point - u2->code_point;
}

const char *unicode_to_kw(unicode code_point)
{
	static char buf[10];
	sprintf(buf, "%%x%06X%%", code_point);
	return buf;
}

const char *unicode_to_pp(unicode cp)
{	
	utf8_to_pp_entry key, *search_result;
	key.code_point = cp;
	search_result = bsearch(&key, utf8_to_pp,
		UTF8_TO_PP_LEN, sizeof(utf8_to_pp_entry), utf8_to_pp_entry_cmp);
	return search_result != 0 ?
		search_result->pp_string :
		unicode_to_kw(cp);
}
/*
 * If invalid UTF-8 is found, output an error message and skip to
 * the next new line.
 */
unicode invalid_utf8(void)
{
	int whatgot;
	fprintf(stderr, "utf8pp: line %d: invalid utf-8 input\n", line);
	utf8pp_error = 1;
	whatgot = getchar();
	while(whatgot != '\n' && whatgot != EOF) {
		whatgot = getchar();
	}
	if(whatgot == '\n') {
		line += 1;
	}
	return whatgot & 0xff;
}

unicode get_code_point(void)
{
	int whatgot, r, l;
	whatgot = getchar();
	if(whatgot == EOF) { return 0; }
	if(whatgot == '\n') { line += 1; }
	r = whatgot & 0xff;
	if(r <= 0x7f) { return r; }
	l = 0;
	while(r & 0x80) {
		r = (r & 0x7f) << 1;
		l += 1;
	}
	if(l > 4) { return invalid_utf8(); }
	r = r >> l;
	while(--l) {
		whatgot = getchar();
		if(whatgot == EOF || ((whatgot & 0xc0) != 0x80)) {
			return invalid_utf8();
		}
		r = (r << 6) | (whatgot & 0x3f);
	}
	return r;
}

void do_utf8_to_pp(void)
{
	unicode cp;
	const char *pp_string;
	cp = get_code_point();
	while(cp) {
		pp_string = unicode_to_pp(cp);
		printf("%s", pp_string);
		cp = get_code_point();
	}
}

void usage(void)
{
	printf("utf8pp"
		": convert UTF-8 to ProofPower extended character format\n");
	printf("utf8pp: usage: utf8pp < input_file > output_file\n");
}

int main (int argc, char *argv[])
{
	line = 1;
	if(argc == 1) {
		do_utf8_to_pp();
		return ferror(stdin) || ferror(stdout) || utf8pp_error;
	} else {
		usage();
		return 0;
	}
}
