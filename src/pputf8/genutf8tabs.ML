(*
 * T]his file generates a C header file convtab.h
 * containing the definition of a table mapping ProofPower extended characters
 * to UTF-8 encoded Unicode equivalents. It also includes code to convert
 * UTF-8 to ProofPower extended characters but that is not currently used.
 *)
local
structure W = Word;
structure C = SML97BasisLibrary.Char;
structure S = SML97BasisLibrary.String;

fun utf8_of_word (w : W.word) : string = (
	S.implode (map (C.chr o W.toInt) (
	if	w <= 0wx7f	(* <= 7 bits *)
	then	[	w]
	else if	w <= 0wx7ff	(* <= 11 bits *)
	then	[	W.orb(0wxc0, W.>>(w, 0wx6)),
			W.orb(0wx80, W.andb(w, 0wx3f))]
	else if	w <= 0wxffff	(* <= 16 bits *)
	then	[	W.orb(0wxe0, W.>>(w, 0wxc)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0), 0wx6)),
			W.orb(0wx80, W.andb(w, 0wx3f))]
	else if	w <= 0wx1fffff	(* <= 21 bits *)
	then	[	W.orb(0wxf0, W.>>(w, 0wx12)),
			W.orb(0wx80, W.>>(W.andb(w, 0wx3f000), 0wxc)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0), 0wx6)),
			W.orb(0wx80, W.andb(w, 0wx3f))]
	else if	w <= 0wx3ffffff	(* <= 26 bits *)
	then	[	W.orb(0wxf8, W.>>(w, 0wx18)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0000), 0wx12)),
			W.orb(0wx80, W.>>(W.andb(w, 0wx3f000), 0wxc)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0), 0wx6)),
			W.orb(0wx80, W.andb(w, 0wx3f))]
	else	[	W.orb(0wxfc, W.>>(w, 0wx1e)),
			W.orb(0wx80, W.>>(W.andb(w, 0wx3f000000), 0wx18)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0000), 0wx12)),
			W.orb(0wx80, W.>>(W.andb(w, 0wx3f000), 0wxc)),
			W.orb(0wx80, W.>>(W.andb(w, 0wxfc0), 0wx6)),
			W.orb(0wx80, W.andb(w, 0wx3f))]))
);


val byte_string_order : string ORDER = (fn s1 => fn s2 =>
	lexicographic (fn c1 => fn c2 => ord c1 - ord c2) (explode s1) (explode s2)
);

val pp_to_utf8_tab : (string * string) list = 
	(sort (pair_order byte_string_order byte_string_order) o
		map (fn (c, w) => (c, utf8_of_word w))) [
	("-",	0wx002212 ),	(* MINUS SIGN *)
	("³",	0wx0000AC ),	(* NOT SIGN *)
	("¸",	0wx0000d7 ),	(* MULTIPLICATION SIGN *)
	("‡",	0wx000393 ),	(* GREEK CAPITAL LETTER GAMMA *)
	("„",	0wx000394 ),	(* GREEK CAPITAL LETTER DELTA *)
	("Š",	0wx000398 ),	(* GREEK CAPITAL LETTER THETA *)
	("Œ",	0wx00039b ),	(* GREEK CAPITAL LETTER LAMDA *)
	("˜",	0wx00039e ),	(* GREEK CAPITAL LETTER XI *)
	("",	0wx0003a0 ),	(* GREEK CAPITAL LETTER PI *)
	("“",	0wx0003a3 ),	(* GREEK CAPITAL LETTER SIGMA *)
	("•",	0wx0003a5 ),	(* GREEK CAPITAL LETTER UPSILON *)
	("†",	0wx0003a6 ),	(* GREEK CAPITAL LETTER PHI *)
	("™",	0wx0003a8 ),	(* GREEK CAPITAL LETTER PSI *)
	("—",	0wx0003a9 ),	(* GREEK CAPITAL LETTER OMEGA *)
	("Á",	0wx0003b1 ),	(* GREEK SMALL LETTER ALPHA *)
	("Â",	0wx0003b2 ),	(* GREEK SMALL LETTER BETA *)
	("Ç",	0wx0003b3 ),	(* GREEK SMALL LETTER GAMMA *)
	("Ä",	0wx0003b4 ),	(* GREEK SMALL LETTER DELTA *)
	("Ú",	0wx0003b6 ),	(* GREEK SMALL LETTER ZETA *)
	("È",	0wx0003b7 ),	(* GREEK SMALL LETTER ETA *)
	("Ê",	0wx0003b8 ),	(* GREEK SMALL LETTER THETA *)
	("É",	0wx0003b9 ),	(* GREEK SMALL LETTER IOTA *)
	("Ë",	0wx0003ba ),	(* GREEK SMALL LETTER KAPPA *)
	("Ì",	0wx0003bb ),	(* GREEK SMALL LETTER LAMDA *)
	("Í",	0wx0003bc ),	(* GREEK SMALL LETTER MU *)
	("Î",	0wx0003bd ),	(* GREEK SMALL LETTER NU *)
	("Ø",	0wx0003be ),	(* GREEK SMALL LETTER XI *)
	("Ð",	0wx0003c0 ),	(* GREEK SMALL LETTER PI *)
	("Ò",	0wx0003c1 ),	(* GREEK SMALL LETTER RHO *)
	("Ó",	0wx0003c3 ),	(* GREEK SMALL LETTER SIGMA *)
	("Ô",	0wx0003c4 ),	(* GREEK SMALL LETTER TAU *)
	("Õ",	0wx0003c5 ),	(* GREEK SMALL LETTER UPSILON *)
	("Ù",	0wx0003c6 ),	(* GREEK SMALL LETTER PHI *)
	("Ñ",	0wx0003c7 ),	(* GREEK SMALL LETTER CHI *)
	("×",	0wx0003c9 ),	(* GREEK SMALL LETTER OMEGA *)
	("Æ",	0wx0003d5 ),	(* GREEK PHI SYMBOL *)
	("Å",	0wx0003f5 ),	(* GREEK LUNATE EPSILON SYMBOL *)
	("°",	0wx002588 ),	(* FULL BLOCK *)
	("ë",	0wx002040 ),	(* CHARACTER TIE *)
	("Ö",	0wx002102 ),	(* DOUBLE-STRUCK CAPITAL C *)
	("î",	0wx002115 ),	(* DOUBLE-STRUCK CAPITAL N *)
	("ð",	0wx002119 ),	(* DOUBLE-STRUCK CAPITAL P *)
	("ó",	0wx00211a ),	(* DOUBLE-STRUCK CAPITAL Q *)
	("¯",	0wx00211d ),	(* DOUBLE-STRUCK CAPITAL R *)
	("ú",	0wx002124 ),	(* DOUBLE-STRUCK CAPITAL Z *)
	("­",	0wx002192 ),	(* RIGHTWARDS ARROW *)
	("ª",	0wx002194 ),	(* LEFT RIGHT ARROW *)
	("ê",	0wx002195 ),	(* UP DOWN ARROW *)
	("ç",	0wx002197 ),	(* NORTH EAST ARROW *)
	("è",	0wx002198 ),	(* SOUTH EAST ARROW *)
	("ï",	0wx0021a0 ),	(* RIGHTWARDS TWO HEADED ARROW *)
	("à",	0wx0021a3 ),	(* RIGHTWARDS ARROW WITH TAIL *)
	("í",	0wx0021a6 ),	(* RIGHTWARDS ARROW FROM BAR *)
	("ù",	0wx0021be ),	(* UPWARDS HARPOON WITH BARB RIGHTWARDS *)
	("ì",	0wx0021bf ),	(* UPWARDS HARPOON WITH BARB LEFTWARDS *)
	("ã",	0wx0021d0 ),	(* LEFTWARDS DOUBLE ARROW *)
	("´",	0wx0021d2 ),	(* RIGHTWARDS DOUBLE ARROW *)
	("¤",	0wx0021d4 ),	(* LEFT RIGHT DOUBLE ARROW *)
	("ß",	0wx0021f8 ),	(* RIGHTWARDS ARROW WITH VERTICAL STROKE *)
	("Ÿ",	0wx0021fb ),	(* RIGHTWARDS ARROW WITH DOUBLE VERTICAL STROKE *)
	("µ",	0wx002200 ),	(* FOR ALL *)
	("¶",	0wx002203 ),	(* THERE EXISTS *)
	("š",	0wx002205 ),	(* EMPTY SET *)
	("",	0wx002208 ),	(* ELEMENT OF *)
	("Ž",	0wx002209 ),	(* NOT AN ELEMENT OF *)
	("…",	0wx002218 ),	(* RING OPERATOR *)
	("±",	0wx002227 ),	(* LOGICAL AND *)
	("²",	0wx002228 ),	(* LOGICAL OR *)
	("¡",	0wx002229 ),	(* INTERSECTION *)
	("À",	0wx00222a ),	(* UNION *)
	("¦",	0wx00225c ),	(* DELTA EQUAL TO *)
	("½",	0wx002260 ),	(* NOT EQUAL TO *)
	("é",	0wx002261 ),	(* IDENTICAL TO *)
	("¼",	0wx002264 ),	(* LESS-THAN OR EQUAL TO *)
	("¾",	0wx002265 ),	(* GREATER-THAN OR EQUAL TO *)
	(" ",	0wx002282 ),	(* SUBSET OF *)
	("ä",	0wx002283 ),	(* SUPERSET OF *)
	("€",	0wx002286 ),	(* SUBSET OF OR EQUAL TO *)
	("å",	0wx002287 ),	(* SUPERSET OF OR EQUAL TO *)
	("Ã",	0wx002291 ),	(* SQUARE IMAGE OF OR EQUAL TO *)
	("«",	0wx002295 ),	(* CIRCLED PLUS *)
	("£",	0wx002296 ),	(* CIRCLED MINUS *)
	("ô",	0wx0022a2 ),	(* RIGHT TACK *)
	("â",	0wx0022a5 ),	(* UP TACK *)
	("¥",	0wx0022c2 ),	(* N-ARY INTERSECTION *)
	("Þ",	0wx0022c3 ),	(* N-ARY UNION *)
	("‰",	0wx0022ce ),	(* CURLY LOGICAL OR *)
	("›",	0wx0022cf ),	(* CURLY LOGICAL AND *)
	("¬",	0wx00231c ),	(* TOP LEFT CORNER *)
	("®",	0wx00231d ),	(* TOP RIGHT CORNER *)
	("¹",	0wx0024c8 ),	(* CIRCLED LATIN CAPITAL LETTER S *)
	("ü",	0wx002500 ),	(* BOX DRAWINGS LIGHT HORIZONTAL *)	
	("Ü",	0wx002502 ),	(* BOX DRAWINGS LIGHT VERTICAL *)	
	("ÿ",	0wx00250c ),	(* BOX DRAWINGS LIGHT DOWN AND RIGHT *)	
	("ˆ",	0wx002514 ),	(* BOX DRAWINGS LIGHT UP AND RIGHT *)
	("÷",	0wx00251c ),	(* BOX DRAWINGS LIGHT VERTICAL AND RIGHT *)	
	("œ",	0wx002550 ),  (* BOX DRAWINGS DOUBLE HORIZONTAL *)
	("",	0wx002552 ),	(* BOX DRAWINGS DOWN SINGLE AND RIGHT DOUBLE *)	
	("’",	0wx0025b7 ),	(* WHITE RIGHT-POINTING TRIANGLE *)
	("ò",	0wx0025c1 ),	(* WHITE LEFT-POINTING TRIANGLE *)
	("û",	0wx0027e6 ),	(* MATHEMATICAL LEFT WHITE SQUARE BRACKET *)
	("ý",	0wx0027e7 ),	(* MATHEMATICAL RIGHT WHITE SQUARE BRACKET *)
	("Ï",	0wx002900 ),	(* RIGHTWARDS TWO-HEADED ARROW WITH VERTICAL STROKE *)
	("þ",	0wx002914 ),	(* RIGHTWARDS ARROW WITH TAIL WITH VERTICAL STROKE *)
	("ž",	0wx002915 ),	(* RIGHTWARDS ARROW WITH TAIL WITH DOUBLE VERTICAL STROKE *)
	("",	0wx002916 ),	(* RIGHTWARDS TWO-HEADED ARROW WITH TAIL *)
	("·",	0wx002981 ),	(* Z NOTATION SPOT *)
	("º",	0wx002982 ),	(* Z NOTATION TYPE COLON *)
	("¨",	0wx002987 ),	(* Z NOTATION LEFT IMAGE BRACKET *)
	("©",	0wx002988 ),	(* Z NOTATION RIGHT IMAGE BRACKET *)
	("Ý",	0wx00298e ),	(* RIGHT SQUARE BRACKET WITH TICK IN BOTTOM CORNER *)
	("Û",	0wx00298f ),	(* LEFT SQUARE BRACKET WITH TICK IN BOTTOM CORNER *)
	("‚",	0wx002a04 ),	(* N-ARY UNION OPERATOR WITH PLUS *)
	("»",	0wx002a3e ),	(* Z NOTATION RELATIONAL COMPOSITION *)
	("á",	0wx002a64 ),	(* Z NOTATION DOMAIN ANTIRESTRICTION *)
	("",	0wx002a65 ),	(* Z NOTATION RANGE ANTIRESTRICTION *)
	("§",	0wx003008 ),	(* LEFT ANGLE BRACKET *)
	("¢",	0wx003009 ),	(* RIGHT ANGLE BRACKET *)
	("–",	0wx01d539 ),	(* MATHEMATICAL DOUBLE-STRUCK CAPITAL B *)
	("æ",	0wx01d53d ),	(* MATHEMATICAL DOUBLE-STRUCK CAPITAL F *)
	("¿",	0wx01d54a ),	(* MATHEMATICAL DOUBLE-STRUCK CAPITAL S *)
	("ƒ",	0wx01d54c ),	(* MATHEMATICAL DOUBLE-STRUCK CAPITAL U *)
	("õ",	0wx00208d ),	(* SUBSCRIPT LEFT PARENTHESIS *)
	("ö",	0wx00208e ),	(* SUBSCRIPT RIGHT PARENTHESIS *)
	("ø",	0wx00002d )	(* HYPHEN-MINUS *)
(*	("‹",	0wx0 ),	*)
(*	("‘",	0wx0 ),	*)
(*	("”",	0wx0 ),	*)
(*	("ñ",	0wx0 ), *)
];

(*
 * The following have no Unicode equivalent, but have equivalent
 * ProofPower forms that do.
 *)
val pp_to_replacement : (string * string) list = 
	map (fn (c, s) => (c, implode (map (lassoc1 pp_to_utf8_tab) (explode s)))) [
	("‹",	"ë/" ),
	("‘",	"¬‰SML " ),
	("”",	"¬‰: " ),
	("ñ",	"¬‰Z ")	
];

(*
 * The following Unicode characters are used in the ISO Z standard,
 * have no ProofPower single character equivalents, but do 
 * have equivalent ASCII keyword forms. (Note that the standard used the
 * wrong double angle brackets, so we support both forms).
 *)
val utf8_to_replacement : (string * string) list = 
		map (fn (w, c) => (utf8_of_word w, c)) [
	(0wx002028,	"÷" ), (* LINE SEPARATOR *)
	(0wx002199,	"ê" ), (* SOUTH WEST ARROW *)
	(0wx002196,	"ê" ), (* NORTH WEST ARROW *)
	(0wx00223c,	"~" ), (* TILDE OPERATOR *)
	(0wx0027ea,	"\037<<\037" ), (* MATHEMATICAL LEFT DOUBLE ANGLE BRACKET *)
	(0wx0027eb,	"\037>>\037" ), (* MATHEMATICAL RIGHT DOUBLE ANGLE BRACKET *)
	(0wx002989,	"(" ), (* Z NOTATION LEFT BINDING BRACKET *)
	(0wx00298a,	")" ), (* Z NOTATION RIGHT BINDING BRACKET *)
	(0wx0029f9,	"\\" ), (* BIG REVERSE SOLIDUS *)
	(0wx00300a,	"\037<<\037" ), (* LEFT DOUBLE ANGLE BRACKET *)
	(0wx00300b,	"\037>>\037" ), (* RIGHT DOUBLE ANGLE BRACKET *)
	(0wx01d538,	"%bbA%" ) (* MATHEMATICAL DOUBLE-STRUCT CAPITAL A *)
];

val pp_to_utf8 : string array =
	PPArray.arrayoflist
		(map (lassoc1 (pp_to_replacement @ pp_to_utf8_tab))
			(map chr (interval 0 255)));

val utf8_to_pp_tab : (string * string) list =
	(sort (pair_order byte_string_order byte_string_order)) 
		(utf8_to_replacement @ map swap pp_to_utf8_tab);

val hex_of_int : int -> string = Int.fmt StringCvt.HEX;

fun hex_of_char (c : char) : string = (
	let	val i = C.ord c;
	in	hex_of_int (i div 16) ^
		hex_of_int (i mod 16)
	end
);

fun c_hex_char_of_char (c : char) : string = (
	"\\x" ^ hex_of_char c
);

fun c_hex_string_of_string (s : string) : string = (
	implode(map c_hex_char_of_char(S.explode s))
);

fun c_pp_to_utf8 (outfile : string) : unit = (
	let	val strm = open_out outfile;
		fun say s = output(strm, s);
		fun aux i = (
			let	val s = PPArray.sub(pp_to_utf8, i);
				val text = c_hex_string_of_string s;
			in	say "\t\"";
				say text;
				(if	i < 255
				then	(say "\",\n";
					aux (i+1))
				else	say "\"\n")
			end
		);
	in	say (
"/*\n * " ^
 outfile ^ ": automatically generated by utf8.ML.\n * " ^
 Date.toString (Date.fromTimeLocal(Time.now())) ^ "\n" ^
" * Conversion from ProofPower characters to UTF-8 strings is done\n" ^
" * by an indexed lookup in the following array:\n" ^
" */\n");
		say "static const char *pp_to_utf8 [256] = {\n";
		aux 0;
		say "};\n";
		close_out strm
	end
);


fun c_utf8_to_pp (outfile : string) : unit = (
	let	val strm = open_out outfile;
		fun say s = output(strm, s);
		fun aux ((s1, s2) :: more) = (
			let	val text1 = c_hex_string_of_string s1;
				val text2 = c_hex_string_of_string s2;
			in	say "\t{\"";
				say text1;
				say "\", \"";
				say text2;
				(case more of
				 _ :: _	=> 	(
					say "\"},\n";
					aux more
				) | _	=>	say "\"}\n")
			end
		) | aux [] = ();
	in	say (
"/*\n * " ^
 outfile ^ ": automatically generated by utf8.ML.\n * " ^
  Date.toString (Date.fromTimeLocal(Time.now())) ^ "\n" ^
" * Conversion from UTF-8 encoded character to a string of 1 or more\n" ^
" * ProofPower extended characters is done by an associative lookup\n" ^
" * in the following sorted array of records:\n" ^
" */\n" ^
"typedef struct {\n" ^
"\tconst char *utf8_string;\n" ^
"\tconst char *pp_string;} utf8_to_pp_entry;\n");
		say "#define UTF8_TO_PP_LEN ";
		say(string_of_int (length utf8_to_pp_tab));
		say "\nstatic utf8_to_pp_entry utf8_to_pp [UTF8_TO_PP_LEN] = {\n";
		aux utf8_to_pp_tab;
		say "};\n";
		close_out strm
	end
);

val _ =
	if length utf8_to_pp_tab <> length pp_to_utf8_tab + length utf8_to_replacement
	then	diag_line "WARNING: duplicate entries lost from utf8_to_pp_tab"
	else	();
in
	val _ = c_pp_to_utf8 "pputf8tab.h";
	val _ = c_utf8_to_pp "utf8pptab.h";
end;
