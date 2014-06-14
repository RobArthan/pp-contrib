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
 * code. It contains an array of records each containing a UTF-8
 * string and the corresponding ProofPower character. The array is sorted by
 * the UTF-8 string and we do the associative lookup with bsearch. A UTF-8
 * string comprising a single ASCII character may haver an entry in the array,
 * but, if not, it will be mapped to itself.
 */
#include "utf8pptab.h"

/*
 * To avoid any possible problems with locales or signed characters
 * we roll our own strcmp.
 */
int utf8_to_pp_entry_cmp(const void *buf1, const void *buf2)
{
	const utf8_to_pp_entry *u1 = buf1, *u2 = buf2;
	const char *s1 = u1->utf8_string, *s2 = u2->utf8_string;
	while(*s1 == *s2 && *s1 != 0) {
		s1 += 1;
		s2 += 1;
	}
	return (((int) *s1) & 0xff) - (((int) *s2) & 0xff);
}

const char *map_utf8_to_pp(const char *utf8)
{	
	utf8_to_pp_entry key, *search_result;
	key.utf8_string = (char*)utf8;
	search_result = bsearch(&key, utf8_to_pp,
		UTF8_TO_PP_LEN, sizeof(utf8_to_pp_entry), utf8_to_pp_entry_cmp);
	return search_result != 0 ?
		search_result->pp_string : /* Supported UTF-8 */
		utf8[1] == 0 ? utf8 : /* Length 1: ASCII */
		"%unsupported_utf8%"; /* Unsupported UTF-8 */
}

char *get_utf8_string(void)
{
	int whatgot, i, len;
	unsigned char c;
	static char result[7];
	whatgot = getchar();
	if(whatgot == EOF) {
		return 0;
	}
	result[0] = c = whatgot;
	len =	c < 0x80 ?  1 :
		c < 0xc0 ? -1 :
		c < 0xe0 ?  2 :
		c < 0xf0 ?  3 :
		c < 0xf8 ?  4 :
		c < 0xfc ?  5 :
		c < 0xfe ?  6 :
		-1;
	if(len < 1) {
		return "invalid_utf8";
	}
	for(i = 1; i < len; i += 1) {
		whatgot = getchar();
		if(whatgot == EOF || ((whatgot & 0xc0) != 0x80)) {
			return "invalid_utf8";
		}
		result[i] = whatgot;
	}
	result[len] = 0;
	return result;
}

static void do_utf8_to_pp(void)
{
	const char *utf8_string, *pp_string;
	utf8_string = get_utf8_string();
	while(utf8_string != 0) {
		pp_string =  map_utf8_to_pp(utf8_string);
		printf("%s", pp_string);
		utf8_string = get_utf8_string();
	}
}

static void usage(void)
{
	printf("utf8pp"
		": convert UTF-8 to ProofPower extended character format\n");
	printf("utf8pp: usage: utf8pp < input_file > output_file\n");
}

int main (int argc, char *argv[])
{
	if(argc == 1) {
		do_utf8_to_pp();
		return ferror(stdin) || ferror(stdout);
	} else {
		usage();
		return 0;
	}
}
