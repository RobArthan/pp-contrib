=IGN
$Id: t011.doc,v 1.5 2006/10/21 16:53:33 rbj01 Exp $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Unifying and Antiunifying Type and Term Nets}
\author{Roger Bishop Jones}
\date{$ $Date: 2006/10/21 16:53:33 $ $}

\makeindex
\usepackage[unicode]{hyperref}

\begin{document}
\vfill
\maketitle
\begin{abstract}
Theorem proving in ProofPower is heavily based on rewriting which is supported by term nets which partially match the rewriting rules against target terms.
To provide a higher level of automation using unification, closer to the power of modern predicate calculus automation present in other implementations of HOL term nets which unify rather than match, and which also produce antiunifiers have been considered here.
This is mainly design, and though there is a very crude implementation, this is for evaluation only and would not deliver reasonable performance.
\end{abstract}
\vfill
\begin{centering}

\href{http://www.rbjones.com/rbjpub/pp/doc/t011.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t011.pdf}

$ $Id: t011.doc,v 1.5 2006/10/21 16:53:33 rbj01 Exp $ $

\bf Copyright \copyright\ : Roger Bishop Jones \\

\end{centering}

\newpage
\tableofcontents

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{Introduction}

=SML
open_theory "basic_hol";
set_pc "basic_hol";
=TEX

\section{LISTS}

The dictionary facilities provided below are given with a simple implementation using lists of pairs for a dictionary.
The operations over these dictionaries often may be applicable for other kinds of lists.
The following signature therefore provides a supplementary selection of operations over lists which are used to implement the dictionary facilities which appear in the next section.

\subsection{Signature ListUtilities2}
=DOC
signature ⦏ListUtilities2⦎ = sig
=DESCRIBE

=ENDDOC

=DOC
val ⦏l_app⦎ : ('a -> 'a) -> string -> (string * 'a) list -> (string * 'a) list;
val ⦏l_app2⦎ : (string * 'a -> 'a) -> string -> (string * 'a) list -> (string * 'a) list;
=DESCRIBE
=ENDDOC

=SML
end; (* of signature ListUtilities2 *)
=TEX

\subsection{Structure ListUtilities2}

=SML
structure ListUtilities2 : ListUtilities2 = struct
=TEX
=SML
fun ⦏l_app⦎ f x [] = fail "ListUtilities2" 100111 [fn y => x]
| l_app f x ((hi, hv)::t) = if hi = x then ((hi, f hv)::t) else (hi, hv)::(l_app f x t);

fun ⦏l_app2⦎ f x [] = fail "ListUtilities2" 100111 [fn y => x]
| l_app2 f x ((h as (hi, hv))::t) = if hi = x then ((hi, f h)::t) else h::(l_app2 f x t);

=IGN
fun (abs : (''a * 'b) list) ⦏modify⦎ ((xy as (x, y)) : ''a * 'b) : (''a * 'b) list = (
	let	fun aux acc [] = rev (xy :: acc)
		|   aux acc ((ab as (a, b)) :: moreabs) = (
			if	a = x
			then	rev acc @ (xy :: moreabs)
			else	aux (ab :: acc) moreabs
		);
	in	aux [] abs
	end
);
=TEX

=SML
end; (* of structure ListUtilities2 *)
=TEX

\section{DICTIONARIES}

\subsection{Mapping Dictionary}

This is an extension to the simple dictionary in dtd/imp001 \cite{ds/fmu/ied/dtd001,ds/fmu/ied/imp001}, but could also be implemented using efficient dictionaries or be given a hybrid implementation.

Strictly extending the signature makes no sense since the simple and efficient dictionaries have disjoint signatures.
This new signature is intended to be relatively independendent of implementation method, so that there may be more than one structure which implements it.

Having decided that a new signature is necessary, I have nevertheless made it as close to the precedent provided by $SimpleDictionary$ as possible.

\subsubsection{Signature}

=DOC
signature ⦏MappingDictionary⦎ = sig
=DESCRIBE
This is a signature for dictionaries which associate values with string keys and which provide facilities for filtering the dictionary and or mapping functions over the dictionary.
=SEEALSO
$Simple_Dictionary$, $EfficientDictionary$.
=FAILURE
100111	Failed to find key ?0.
=ENDDOC

=DOC
type (''k,'a) ⦏M_DICT⦎;
val ⦏initial_m_dict⦎ : (''k,'a) M_DICT;
val ⦏m_lookup⦎ : ''k ->(''k,'a) M_DICT -> 'a OPT;
val ⦏m_enter⦎ : ''k -> 'a -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_list_enter⦎ : (''k * 'a) list -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_extend⦎ : ''k -> 'a -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_list_extend⦎ : (''k * 'a) list -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_delete⦎ : ''k -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
=DESCRIBE
\begin{description}
\item $initial\_m\_dict$ is the empty dictionary which associates nothing with any key value.
\item $m\_lookup$ $key$ $dict$ retrieves value, if any, stored in $dict$ under key $key$.
\item $m\_enter$ $key$ $val$ $dict$ gives a dictionary which associates $val$ with the key $key$ and otherwise is the same as the original dictionary $dict$.
\item $m\_extend$ $key$ $val$ $dict$ is similar to $m\_enter$ except that it will raise an exception if $key$ is already associated with a value in $dict$.
\item $list\_m\_enter$ and $list\_m\_extend$ enter into or extend by a list of string value pairs.
\item $m\_delete$ $key$ $dict$ gives a dictionary which associates no value with the key $key$ and otherwise is the same as the original dictionary $dict$.
\end{description}
=ENDDOC

=DOC
val ⦏m_app⦎ : ''k -> ('a -> 'a) -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_mapfilter⦎ : ((''k * 'a) -> 'b) -> (''k,'a) M_DICT -> (''k,'b) M_DICT;
val ⦏m_mapfilter_list⦎ : ((''k * 'a) -> 'b) -> (''k,'a) M_DICT -> 'b list;
val ⦏m_list⦎ : (''k,'a) M_DICT -> (''k * 'a) list;
val ⦏m_combine⦎ : ('a OPT * 'b OPT -> 'c OPT)
		-> (''k,'a) M_DICT -> (''k,'b) M_DICT -> (''k,'c) M_DICT;
val ⦏m_override⦎ : (''k,'a) M_DICT -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
val ⦏m_merge⦎ : (''k,'a) M_DICT -> (''k,'a) M_DICT -> (''k,'a) M_DICT;
=DESCRIBE
\begin{description}
\item $m\_app$ $key$ $f$ gives a dictionary which associates with the key $key$ the result of applying the function $f$ to the value associated with key $key$ in dictionary $dict$, and is otherwise the same as $dict$.
\item $m\_mapfilter$ maps a function over the contents of a dictionary.
If the function raises exception Fail this is caught and causes the relevant entry to be omitted from the new dictionary.
\item $m\_mapfilter\_list$ is the simlar to $m\_mapfilter$ except that it returns a list rather than a dictionary.
\item $m\_list$ is the same as $m\_mapfilter\_list$ applied to the function $fn  x => x$.
\item $m\_combine$ $fun$ $dict1$ $dict2$ gives the dictionary obtained by combining using $fun$ the entries in each dictionary for every key which occurs in either.
\item $m\_override$ $dict1$ $dict2$ gives the dictionary obtained by entering (as $m\_enter$) into $dict1$ every $key$ $value$ pair present in $dict2$.
\item $m\_merge$ $dict1$ $dict2$ gives the dictionary obtained by extending (as $m\_extend$) into $dict1$ every $key$ $value$ pair present in $dict2$.
\end{description}
=ENDDOC

=SML
end (* of MappingDictionary signature *);
=TEX

\subsubsection{Simple Implementation}

This is implemented in a similar manner to SimpleDictionary, representing the dictionary as a list of key/value pairs.

I would have actually used $SimpleDictionary$ to implement it if I could have, but the visibility of the representation type is necessary for the extra functionality, so this could not be done.

=SML
structure ⦏SimpleMDictionary⦎ : MappingDictionary = struct
=TEX

=SML
type (''k,'a) M_DICT = (''k * 'a) list;
=TEX

The implementation of the functions corresponding to those of $SimpleDictionary$ is copied from imp001 \cite{ds/fmu/ied/imp001}, the only changes being to the names of the functions.

\ignore{
We define a simple dictionary to be a list of
pairs in UtilitySharedTypes.
The functions for accessing and modifying
dictionaries are essentially just interfaces to the
partial function operations defined in
previous sections:

$m\_lookup$ implements application (of the dictionary
viewed as a partial function):
=SML
fun ⦏m_lookup⦎ (k : ''k) (dict : (''k,'a) M_DICT) : 'a OPT = (
	lassoc5 dict k
);
=TEX
$m\_enter$ implements overwriting by a singleton function:
=SML
fun ⦏m_enter⦎ (k : ''k) (a : 'a) (dict : (''k,'a) M_DICT) : (''k,'a) M_DICT = (
	dict overwrite (k, a)
);
=TEX
$m\_extend$ implements extension by a singleton function,
that is to say it is like $m\_enter$  but raises an
exception if the new argument is already
in the domain of the dictionary:
=SML
fun ⦏m_extend⦎ (k : ''k) (a : 'a) (dict : (''k,'a) M_DICT) : (''k,'a) M_DICT = (
	case lassoc5 dict k of
	Value _ => fail "m_extend" 1014 []
	| Nil => (k,a) :: dict
);
=TEX
$m\_delete$ deletes an element of the domain of a dictionary.
If the element is not in the domain it returns the
dictionary unchanged.
=SML
fun ⦏m_delete⦎ (k : ''k) (dict : (''k,'a) M_DICT) : (''k,'a) M_DICT = (
	dict drop (fn (k', _) => k' = k)
);
=TEX
$m\_merge$ extends one dictionary by another.
An exception will be raised if the domains of the
two dictionaries have elements in common.
=SML
fun ⦏m_merge⦎ (dict1: (''k,'a) M_DICT)
	(dict2 : (''k,'a) M_DICT) : (''k,'a) M_DICT = (
	fold (uncurry(uncurry m_extend)) dict1 dict2
);
=TEX
The initial value of the dictionary is just the empty list.
=SML
val ⦏initial_m_dict⦎ : (''k,'a) M_DICT = [];
=TEX
}%ignore

The additional functions are implemented as follows:

=SML
fun ⦏m_list_enter⦎ l = fold (fn ((s, v), d) => m_enter s v d) l;
fun ⦏m_list_extend⦎ l = fold (fn ((s, v), d) => m_extend s v d) l;
=TEX

=SML
fun ⦏m_app⦎ tag f ([]: (''k,'a) M_DICT) : (''k,'a) M_DICT
	= fail "MappingDictionary" 100111 []
|   m_app tag f ((he as (ht,hv))::t)
	=	if ht = tag
		then (ht, f hv)::t
		else (he :: m_app tag f t);
fun mfa f (k,v) = (k, f(k,v));
fun ⦏m_mapfilter⦎ f (d: (''k,'a) M_DICT) : (''k,'b) M_DICT = mapfilter (mfa f) d;
val ⦏m_mapfilter_list⦎ : ((''k * 'a) -> 'b) -> (''k,'a) M_DICT -> 'b list
	= mapfilter;
fun ⦏m_list⦎ (dict: (''k,'a) M_DICT) : (''k * 'a) list = dict;

fun ⦏m_combine⦎ f d1 d2 =
 let fun	aux acc ((s,v)::t) [] =
		let val acc' = case f (Value v, Nil) of
				  Value v' => ((s, v')::acc)
				| Nil => acc
		in aux acc' t []
		end
     |	 aux acc [] ((s,v)::t) =  
 		let val acc' = case f (Nil, Value v) of
				  Value v' => ((s, v')::acc)
				| Nil => acc
		in aux acc' [] t
		end
     |	 aux acc ((s1,v1)::t1) ((s2,v2)::t2) =
		if s1 = s2
		then	let val acc' = case f (Value v1, Value v2) of
				  Value v' => ((s1, v')::acc)
				| Nil => acc
			in aux acc' t1 t2
			end
		else	aux acc ((s1,v1)::t1) t2
     |	aux acc [] [] = acc
 in aux [] d1 d2
 end;

fun ⦏m_override⦎ (dict1 : (''k,'a) M_DICT) (dict2 : (''k,'a) M_DICT) : (''k,'a) M_DICT = (
	fold (uncurry(uncurry m_enter)) dict1 dict2);
=TEX

=SML
end (* of SimpleMDictionary *);
=TEX

\subsection{List Indexed Dictionary}

\subsubsection{Signature}

=DOC
signature ⦏ListIndexDictionary⦎ = sig
=DESCRIBE
Holds a set of Standard ML functions concerned with managing families of values indexed by lists of strings.
=USES
For use in implementing generic discrimination nets.
The main distinctive features are:
\begin{itemize}
\item indexed by lists of strings
\item muliple values can be saved under each key
\item provides facilities for mapping functions and/or filters over the entries
\end{itemize}

The motivation for this facility is to support saving data indexed by structured entities such as {\it TYPE}s and {\it TERM}s is such a way that computation over the entire set of key values can be done efficiently.
The kind of computation we have in mind here is unification, though any computation which can be accomplished on a string stream encoding of a structured value would also be possible.
The idea is to be able to select from the dictionary and perform some computation on all the values whose index is unifiable with a given {\it TYPE} or {\it TERM}, in such a way that common initial segments of the required computations are not repeated for structures which share that initial segment of structure.

The main differences from the {\it MappingDictionary} signature are therefore, firstly that lists of strings are used as key values, and secondly that mapping functions take these keys one item at a time, and the intermediate values computed can be reused for every key value sharing that initial segment of the list.
=SEEALSO
$MappingDictionary$.
=ENDDOC

=DOC
type ⦏(''k,'a) LI_DICT⦎;
val ⦏initial_li_dict⦎ : (''k,'a) LI_DICT;
val ⦏li_lookup⦎ : ''k list -> (''k,'a) LI_DICT -> 'a list;
val ⦏li_enter⦎ : ''k list -> 'a -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
val ⦏li_enter_list⦎ : ''k list -> 'a list -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
val ⦏li_delete⦎ : ''k list -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
val ⦏li_replace⦎ : ''k list -> 'a list -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
val ⦏li_list⦎ : (''k,'a) LI_DICT -> (''k list * 'a list) list;
=GFT
val ⦏li_merge⦎ : (''k,'a) LI_DICT -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
=DESCRIBE
\begin{description}
\item [$initial\_li\_dict$] is the empty list indexed dictionary.
\item [$li\_lookup$ $taglist$ $dict$] returns the values held in $dict$ under the index $taglist$.
\item [$li\_enter$ $taglist$ $value$ $dict$] adds $value$ to the front of the list of elements held in $dict$ under the index $taglist$.
\item [$li\_enter\_list$ $taglist$ $valuelist$ $dict$] appends $valuelist$ to the front of the list of elements held in $dict$ under the index $taglist$.
\item [$li\_delete$ $taglist$ $dict$] removes all the values associated with $taglist$ in $dict$.
\item [$li\_replace$ $taglist$ $valuelist$ $dict$] replaces the list of values associated with $taglist$ in $dict$ with $valuelist$.
\item [$li\_list$ $dict$] returns a list of pairs of tag lists and value lists corresponding to the entire content of the dictionary.
\item [$li\_merge$ $dict1$ $dict2$] constructs a dict in which the list of values associated with any taglist is the list of values associate with that taglist in $dict1$ appended to the list of values associated with that taglist in $dict2$.
\end{description}
=ENDDOC

=DOC
datatype (''k, 'a, 'b) LIDFUN =	LidRetain
		|	LidDiscard
		|	LidFun of {linode	: ''k -> (''k, 'a, 'b) LIDFUN,
				lileaf	: ('a list) -> 'b};
val ⦏li_mapfilter⦎ : (''k,'a,'b list) LIDFUN -> (''k,'a) LI_DICT -> (''k,'b) LI_DICT;
val ⦏li_mapfilter2⦎ : (''k,'a,'a list) LIDFUN -> (''k,'a) LI_DICT -> (''k,'a) LI_DICT;
val ⦏li_mapfilter_list⦎ : (''k,'a,'b) LIDFUN -> (''k,'a) LI_DICT -> 'b list;
=DESCRIBE
These functions are designed to support efficient processing of the entire dictionary using functions which process a stream of tag values.
The datatype {\it LIDFUN} is concocted to support such applications, and the generic trawling/mapping/filtering operations expect a {\it LIDFUN} as a parameter.
To have a non-trivial effect a {\it LidFun} would be supplied and the tags would be sucessively applied to the {\it linode} components of a succession of {\it LIDFUN}s until a leaf is found which is then transformed by the {\it lileaf} component of the last {\it LidFun}.
This process is effectively repeated for each path in the dictionary, except that paths sharing an initial segment will also share the computation associated with that initial segment (side effects are not intended).
The two other kinds of {\it LIDFUN} allow this process to be curtailed.
When a {\it LidFun} {\it linode} returns a {\it LidDiscard} then the result is as if there were no paths in the original dictionary with that initial path segment.
When a {\it LidFun} {\it linode} is given a tag and returns a {\it LidRetain} then the entire subtree with that initial path segment is to be retained unchanged (the only operator whose type is compatible with the use of {\it LidRetain} is {\it li\_mapfilter2}, others will raise an exception if it arises).

\begin{description}
\item [$li\_mapfilter$ $lidfun$ $dict$] yields a new dictionary in which, against any taglist is held the value obtained by submitting the first value in each taglist to the $linode$ component of the $lidfun$ argument yeilding a new {\it LIDFUN}, submitting the next string to the $linode$ component of that $LIDFUN$ and so on until reaching a leaf, at which point the $'a list$ stored under that taglist is supplied to the $lileaf$ component of the current $LIDFUN$.
If at any point an application of a $LIDFUN$ raises a {\it Fail} exception then no values with a $taglist$ which has an initial segment corresponding to the tags so far processed will appear in the resulting dictionary.
If any other exception is raised it will not be trapped.
For a pure filtering operation the {\it lileaf} component of the {\it LIDFUN} argument should be the identity function.
\item [$li\_mapfilter\_list$ $lidfun$ $dict$] is similar to {\it li\_mapfilter} except that the results of applying the {\it lileaf} components of the {\it LIDFUN} are returned as a list rather than a dictionary.
\end{description}
=FAILURE
100112	LidRetain encountered by {\it li\_mapfilter}
=ENDDOC

=SML
end (* of ListIndexDictionary signature *);
=TEX

=SML
structure ⦏SimpleLIDictionary⦎ : ListIndexDictionary = struct
open SimpleMDictionary;
=TEX

\ignore{

=SML
datatype (''k,'a) ⦏LI_DICT⦎ = LiDict of {leaf: 'a list, mdict: (''k,(''k,'a) LI_DICT) M_DICT};
val ⦏initial_li_dict⦎ = LiDict {leaf = [], mdict = initial_m_dict};
datatype (''k, 'a, 'b) LIDFUN =	LidRetain
		|	LidDiscard
		|	LidFun of {linode	: ''k -> (''k, 'a, 'b) LIDFUN,
				lileaf	: ('a list) -> 'b};
=TEX

=SML
fun ⦏li_lookup⦎ [] (LiDict x) = #leaf x
 |  li_lookup (h::t) (LiDict x) =
	(case m_lookup h (#mdict x) of
			Nil => []
		| 	Value lidict => li_lookup t lidict);

fun ⦏li_enter_list⦎ ([]:''k list) (vl:'a list) (LiDict {leaf, mdict}) =
		LiDict {leaf = vl @ leaf, mdict = mdict}
 |  li_enter_list (tagl as (tagh::tagt)) vl (LiDict {leaf, mdict}) =
		LiDict {leaf = leaf, mdict = m_app tagh (li_enter_list tagt vl) mdict};
 
fun ⦏li_enter⦎ (sl:''k list) (v:'a) = li_enter_list sl [v];
=TEX

=SML
fun ⦏li_delete⦎ ([]:''k list) (LiDict {leaf, mdict}) =
		LiDict {leaf = [], mdict = mdict}
 |  li_delete (tagl as (tagh::tagt)) (dict as LiDict {leaf, mdict}) =
		LiDict {leaf = leaf, mdict = m_app tagh (li_delete tagt) mdict}
	handle ex => if area_of ex = "MappingDictionary" then dict
		else pass_on ex "" "";

fun ⦏li_replace⦎ ([]:''k list) (vl:'a list) (LiDict {leaf, mdict}) =
		LiDict {leaf = vl, mdict = mdict}
 |  li_replace (tagl as (tagh::tagt)) vl (LiDict {leaf, mdict}) =
		LiDict {leaf = leaf, mdict = m_app tagh (li_replace tagt vl) mdict};
=TEX

=SML
fun ⦏li_mapfilter⦎ LidRetain lid = fail "SimpleLIDictionary" 100112 []
| li_mapfilter LidDiscard lid = initial_li_dict
| li_mapfilter (lidf as LidFun {linode, lileaf}) (lid as LiDict {leaf, mdict})
	= let	val leaf' = lileaf leaf
		fun aux (tag, lid2) = li_mapfilter (linode tag) lid2 
		val mdict' = m_mapfilter aux mdict
	in LiDict {leaf = leaf', mdict = mdict'}
	end;

fun ⦏li_mapfilter2⦎ LidRetain lid = lid
| li_mapfilter2 LidDiscard lid = initial_li_dict
| li_mapfilter2 (lidf as LidFun {linode, lileaf}) (lid as LiDict {leaf, mdict}) =
	let	val leaf' = lileaf leaf
		fun aux (tag, lid2) = li_mapfilter (linode tag) lid2 
		val mdict' = m_mapfilter aux mdict
	in LiDict {leaf = leaf', mdict = mdict'}
	end;
=TEX

=SML
fun ⦏li_mapfilter_list⦎ LidRetain lid = fail "SimpleLIDictionary" 100112 []
| li_mapfilter_list LidDiscard lid = []
| li_mapfilter_list (lidf as LidFun {linode, lileaf}) (lid as LiDict {leaf, mdict}) =
	let	val leaf' = lileaf leaf
		fun aux (tag, lid2) = li_mapfilter_list (linode tag) lid2 
		val mdict' = flat (m_mapfilter_list aux mdict)
	in	leaf' :: mdict'
	end;

fun ⦏list_lidfun⦎ path =
	LidFun {	linode = fn tag => list_lidfun (tag::path),
		lileaf = fn leaf => (rev path, leaf)};

fun ⦏li_list⦎ lid = li_mapfilter_list (list_lidfun []) lid;
=IGN
fun ⦏li_merge⦎ (lid1 as LiDict {leaf, mdict}) (lid2 as LiDict {leaf, mdict}) =
	let val leaf' = leaf1 @ leaf2
	    fun aux tag = 
		LiDict {leaf = vl, mdict = mdict}
=TEX

}%ignore

=SML
end (* of SimpleLIDictionary *);
open SimpleLIDictionary;
=TEX

\section{UNIFYING STORES}

=DOC
signature ⦏UNet⦎ = sig
=DESCRIBE
This is the signature of a structure providing facilities similar to those provided by NetTools except that lookup involves unification and returns all items indexed by styructures which are unifiable with the lookup structure.
The results include the unifying substitutions and an anti-unifier of the matching values.

Though in the target applications the indexes are HOL terms this interface is less specific.
It is expected that the structure involved is coded as a list of tag values, the type of which is only partly specified here.
Sufficient tag structure is specified to pernit unification, with polymorphic slots for application specific structure the details of which do not affect the unification algorithm.
=ENDDOC

=DOC
type ('a, 'b)⦏UTAG⦎
type ('a, 'b, 'c)⦏UNET⦎;
type ('a, 'b)⦏USUBS⦎;
=DESCRIBE
Type $('a, 'b)UTAG$ is a type of tags, lists of which may be used to represent various kinds of structures when the type parameters are suitably instantiated.

$('a, 'b, 'c)UNET$ is the type of a unifying net storing values of type $'c$ indexed by lists of tags of type $('a, 'b)UTAG$.

$('a, 'b)USUBS$ is a value which represents unifying substitutions.
=ENDDOC

=DOC
val ⦏mk_uterm⦎ : (TERM * TYPE list * TERM list * TYPE list * TERM list)
	-> UTERM;
val ⦏dest_uterm⦎ : UTERM
	-> (TERM * TYPE list * TERM list * TYPE list * TERM list);
=DESCRIBE
The interfaces to unifying term net facilities make use of the type $UTERM$, which stands for $Unifiable Term$, and left undetermined by the signature to allow optimisation of this type.

The functions $mk\_uterm$ and $dest\_uterm$ provide the external methods for assembling and disassembling $UTERM$s.
The components are:
\begin{enumerate}
\item a term for unification
\item a list of type variables which are to be avoided when creating new type variables
\item a list of term variables which are to be avoided when creating new term variables
\item a list of type variables which can be instantiated during unification
\item a list of term variables which can be instantiated during unification
\end{enumerate}

=ENDDOC

=DOC
val ⦏empty_unet⦎ : ('a, 'b, 'c) UNET;
val ⦏make_utmnet⦎ : (('a,'b)UTAG * 'c) list -> ('a,'b,'c) UNET;
val ⦏unet_enter⦎ : ('a,'b,'c) UNET -> (('a,'b)UTAG * 'c) -> ('a,'b,'c)UNET;
val ⦏list_utmnet_enter⦎ : ('a,'b,'c) UNET -> (('a,'b)UTAG * 'c) list -> ('a,'b,'c)UNET;
=DESCRIBE
$empty\_unet$ gives an empty unet, the type parameters are the type of the nodes and leaves of the tag types and the type of the values to be stored in the unet.
$make\_unet$ takes a list of index/value pairs and inserts them into an empty utmnet.
$unet\_enter$ enters a single new value into a utmnet, $list\_unet\_enter$ adds a list of new entries.

The indexing term must be supplied together with information controlling unification which consists of:
\begin{enumerate}
\item a list of type variables which should be avoided
\item a list of term variables which should be avoided
\item the list of type variables which may be instantiated
\item the list of term variables which may be instantiated
\end{enumerate}
=ENDDOC
=DOC
val ⦏utmnet_content⦎ : ('a UTMNET) -> (UTERM * 'a)list;
val ⦏utmnet_lookup⦎ : ('a UTMNET) -> UTERM
		-> ((UTMSUBST * UTERM * UTMSUBST * 'a)list * UTMSUBST);
val ⦏utmnet_map_filter⦎ : ('a UTMNET) -> ((UTERM * 'a) -> 'b)
		-> UTERM -> ('b UTMNET);
val ⦏utmnet_map⦎ : ('a UTMNET) -> ((UTERM * 'a) -> 'b) -> ('b UTMNET);
val ⦏utmnet_filter⦎ : ('a UTMNET) -> UTERM -> ('a UTMNET);
val ⦏utmnet_fold⦎ : (((UTERM * 'a) * 'b) -> 'b) -> ('a UTMNET) -> 'b -> 'b;
=DESCRIBE
$utmnet\_content$ is the inverse of $make\_utmnet$.

$utmnet\_lookup$ $net$ $uterm$ will return a list of the values entered into $net$
that were indexed by $uterm$s which can be unified with $uterm$.

Each value is returned with the following information:
\begin{enumerate}
\item a substitution which may be applied to the search uterm to unify it with the relevant index uterm
\item an index uterm found to be unifiable with the search uterm
\item a substitution which may be applied to the index uterm to unify it with the search uterm
\item the value associated with the index entry
\end{enumerate}
One further substitution is returned, which instantiates the search uterm to the anti-unifier of the returned terms.
This is not guaranteed to be the most specific antiunifier, some implementations may decline to antiunify and should then return the null substitution.

If $utmnet\_lookup$ returns more than one value, then the only
ordering on the resulting values specified is that if two entries are made into the net with the same index term, then if the $net\_lookup$ term matches the index term then the second entered value will be returned before the first in the list of matches.

$utmnet\_map\_filter$ filters a $UNET$ retaining only items indexed by terms which are unifiable with its argument, and applies the supplied function to the index/value pair replacing the value with the result.
If the function fails then the index/value pair is discarded.

$utmnet\_filter$ is the special cases of $utmnet\_map\_filter$ in which the map is the right projection function.

$utmnet\_map$ is the special cases of $utmnet\_map\_filter$ in which the function is applied to the entire net, the only items dropped being those on which the function fails.

$utmnet\_fold f utmn c$ folds the function over the values in the termnet with initial value c.
=ENDDOC


=SML
end; (* of signature UNet *)
=TEX


=SML
structure SimpleUNet : UNet = struct

open SimpleLIDictionary;
=TEX

=SML
datatype ('a,'b)UTAG =
		UtNode of 'a
	|	UtLeaf of 'b
	|	UtVb of string
	|	UtBv of string
	|	UtIv of string
	|	UtEnd;

type ('a,'b,'c)UNET = (('a,'b)UTAG, 'c) LI_DICT;

type ('a,'b)USUBST = (string * ('a,'b)UTAG list) list;
=TEX

=IGN
val ⦏empty_unet⦎ : (''a, ''b, 'c) UNET
	= initial_li_dict: ((''a,''b)UTAG,'c)LI_DICT;
val ⦏make_unet⦎ : (('a,'b)UTAG * 'c) list -> ('a,'b,'c) UNET
	=;
val ⦏unet_enter⦎ : ('a,'b,'c) UNET -> (('a,'b)UTAG * 'c) -> ('a,'b,'c)UNET;
val ⦏list_utmnet_enter⦎ : ('a,'b,'c) UNET -> (('a,'b)UTAG * 'c) list -> ('a,'b,'c)UNET;
=TEX

=SML
end (* of structure SimpleNet *)
=TEX

\section{UNIFYING TERM NETS}

=DOC
signature ⦏TermNet⦎ = sig
=DESCRIBE
This is the signature of a structure providing facilities similar to those provided by NetTools except that lookup involves unification and returns all items indexed by terms which are unifiable with the lookup term.
The results include the unifying substitutions and an anti-unifier of the matching terms.
=ENDDOC

=DOC
type ⦏UTERM⦎
type 'a ⦏UTMNET⦎;
type ⦏UTMSUBST⦎;
=DESCRIBE
$'a UTMNET$ is the type of a unifying term net storing values of type $'a$ indexed by terms.

$UTMSUBST$ is a value which represents unifying substitutions.
=ENDDOC

=DOC
val ⦏mk_uterm⦎ : (TERM * TYPE list * TERM list * TYPE list * TERM list)
	-> UTERM;
val ⦏dest_uterm⦎ : UTERM
	-> (TERM * TYPE list * TERM list * TYPE list * TERM list);
=DESCRIBE
The interfaces to unifying term net facilities make use of the type $UTERM$, which stands for $Unifiable Term$, and left undetermined by the signature to allow optimisation of this type.

The functions $mk\_uterm$ and $dest\_uterm$ provide the external methods for assembling and disassembling $UTERM$s.
The components are:
\begin{enumerate}
\item a term for unification
\item a list of type variables which are to be avoided when creating new type variables
\item a list of term variables which are to be avoided when creating new term variables
\item a list of type variables which can be instantiated during unification
\item a list of term variables which can be instantiated during unification
\end{enumerate}

=ENDDOC

=DOC
val ⦏empty_utmnet⦎ : 'a UTMNET;
val ⦏make_utmnet⦎ : (UTERM * 'a) list -> ('a UTMNET);
val ⦏utmnet_enter⦎ : ('a UTMNET) -> (UTERM * 'a) -> ('a UTMNET);
val ⦏list_utmnet_enter⦎ : ('a UTMNET) -> (UTERM * 'a) list -> ('a UTMNET);
=DESCRIBE
$empty\_utmnet$ gives an empty utmnet, the type parameter is the type of the values to be stored in the utmnet.
$make\_utmnet$ takes a list of index/value pairs and inserts them into an empty utmnet.
$utmnet\_enter$ enters a single new value into a utmnet, $list\_utmnet\_enter$ adds a list of new entries.

The indexing term must be supplied together with information controlling unification which consists of:
\begin{enumerate}
\item a list of type variables which should be avoided
\item a list of term variables which should be avoided
\item the list of type variables which may be instantiated
\item the list of term variables which may be instantiated
\end{enumerate}
=ENDDOC

=DOC
val ⦏utmnet_content⦎ : ('a UTMNET) -> (UTERM * 'a)list;
val ⦏utmnet_lookup⦎ : ('a UTMNET) -> UTERM
		-> ((UTMSUBST * UTERM * UTMSUBST * 'a)list * UTMSUBST);
val ⦏utmnet_map_filter⦎ : ('a UTMNET) -> ((UTERM * 'a) -> 'b)
		-> UTERM -> ('b UTMNET);
val ⦏utmnet_map⦎ : ('a UTMNET) -> ((UTERM * 'a) -> 'b) -> ('b UTMNET);
val ⦏utmnet_filter⦎ : ('a UTMNET) -> UTERM -> ('a UTMNET);
val ⦏utmnet_fold⦎ : (((UTERM * 'a) * 'b) -> 'b) -> ('a UTMNET) -> 'b -> 'b;
=DESCRIBE
$utmnet\_content$ is the inverse of $make\_utmnet$.

$utmnet\_lookup$ $net$ $uterm$ will return a list of the values entered into $net$
that were indexed by $uterm$s which can be unified with $uterm$.

Each value is returned with the following information:
\begin{enumerate}
\item a substitution which may be applied to the search uterm to unify it with the relevant index uterm
\item an index uterm found to be unifiable with the search uterm
\item a substitution which may be applied to the index uterm to unify it with the search uterm
\item the value associated with the index entry
\end{enumerate}
One further substitution is returned, which instantiates the search uterm to the anti-unifier of the returned terms.
This is not guaranteed to be the most specific antiunifier, some implementations may decline to antiunify and should then return the null substitution.

If $utmnet\_lookup$ returns more than one value, then the only
ordering on the resulting values specified is that if two entries are made into the net with the same index term, then if the $net\_lookup$ term matches the index term then the second entered value will be returned before the first in the list of matches.

$utmnet\_map\_filter$ filters a $UNET$ retaining only items indexed by terms which are unifiable with its argument, and applies the supplied function to the index/value pair replacing the value with the result.
If the function fails then the index/value pair is discarded.

$utmnet\_filter$ is the special cases of $utmnet\_map\_filter$ in which the map is the right projection function.

$utmnet\_map$ is the special cases of $utmnet\_map\_filter$ in which the function is applied to the entire net, the only items dropped being those on which the function fails.

$utmnet\_fold f utmn c$ folds the function over the values in the termnet with initial value c.
=ENDDOC


=SML
end; (* of signature TermNet *)
=TEX

The structure $CrudeUnifyNet$ is an implementation of signature $UnifyNet$ which represents a net as a list of pairs, uses the unification algorithm from the resolution structure and returns the search term as antiunifier.
(this is to permit experimentation with the functionality of backchaining before getting into the details of efficient unification nets).

=SML
structure ⦏CrudeTermNet⦎ : TermNet = struct
=TEX

\ignore{

=SML
open Resolution; open Unification;
=TEX

=SML
type UTERM = TERM * TYPE list * TERM list * TYPE list * TERM list;
type UTMSUBST = (TYPE * TYPE) list * (TERM * TERM) list;
type 'a UTMNET = (UTERM * 'a) list;
=TEX

=SML
fun mk_uterm x = x;
fun dest_uterm x = x;
=TEX

=SML
val empty_utmnet = [];
fun make_utmnet l = l;
fun utmnet_enter utmn e = e :: utmn;
fun list_utmnet_enter utmn le = foldl (op ::) utmn le;
=TEX

=SML
fun utmnet_content utmn = utmn;

fun utm_unify
	(tm1, atyvs1, atmvs1, ityvs1, itmvs1)
	(tm2, atyvs2, atmvs2, ityvs2, itmvs2) =
 let	val subs = new_subs 100;
	val atyvs = atyvs1 @ atyvs2;
	val atmvs = atmvs1 @ atmvs2;
	val op1 = (tm1, itmvs1, ityvs1);
	val op2 = (tm2, itmvs2, ityvs2);
 in term_unify subs atyvs atmvs (op1, op2)
 end;

fun utmnet_lookup utmn sutm =
 let	fun aux (iutm, a) =
	 let	val (s1, s2) = utm_unify sutm iutm
	 in	(s1, iutm, s2, a)
	 end;
	val resl = mapfilter aux utmn;
 in	(resl, ([], []))
 end;

fun utmnet_map_filter utmn f sutm =
 let	val (utm', aus) = utmnet_lookup utmn sutm;
	fun aux (_, utm, _, res) = (utm, f (utm, res))
 in mapfilter aux utm'
 end;
	
fun utmnet_map utmn f =
 let	fun aux (it, v) = (it, f (it,v))
 in	mapfilter aux utmn
 end;

fun utmnet_filter utmn sutm =
 let	val (utm', aus) = utmnet_lookup utmn sutm;
	fun aux (_, utm, _, res) = (utm, res)
 in mapfilter aux utm'
 end;

fun utmnet_fold f u = fold f (utmnet_content u);
=TEX

}%ignore

=SML
end; (* of structure CrudeTermNet *)
=TEX



=SML
structure ⦏UNet⦎ : UNet
=TEX

=SML
end; (* structure UNet *)
=TEX

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
