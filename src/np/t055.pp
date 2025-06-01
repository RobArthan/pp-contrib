=TEX
% $Id: t055.tex $

\documentclass[11pt]{article}
\usepackage{latexsym}
\usepackage{rbj}

\usepackage{fontspec}
\setmainfont[]{ProofPowerSerif}

\ftlinepenalty=9999
\usepackage{A4}

% the following two modal operators come from the amsfonts package
%\def\PrKI{\Diamond}	%Modify printing for \250
%\def\PrKJ{\Box}		%Modify printing for \251

%\def\PrIO{\notin}

%\def\PrJA{\|-}		%Modify printing for  (syntactic consequence)
%\def\PrJI{\models}	%Modify printing for  (semantic entailment)
%\def\PrJO{\prec}	%Modify printing for \236 (semantic entailment)

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\def\thyref#1{Appendix \ref{#1}}

%\def\ExpName{\mbox{{\sf exp}}}
%\def\Exp#1{\ExpName(#1)}

\title{Unicode Characters in ProofPower through Lualatex}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}, pdffitwindow=false, pdfkeywords=RogerBishopJones}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}
\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This document serves to establish what characters render like in utf8 ProofPower documents prepared using lualatex.
\end{abstract}
\vfill

\begin{centering}
{\footnotesize

Created 2019

\input{t046i.tex}

\href{http://www.rbjones.com/rbjpub/pp/doc/t055.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t055.pdf}

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}

\thispagestyle{empty}
\end{titlepage}

\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\section{Prelude}


\section{Changes}

\subsection{Recent Changes}


\subsection{Changes Under Consideration}


\subsection{Issues}

See also Section \ref{POSTSCRIPT}.

\section{Introduction}

\ignore{
=VDUMP t046i.tex
=TEX
}%ignore



\section{Mathematical operators and symbols in Unicode}

From Wikipedia, the free encyclopedia, transcribed into lualatex to determine which characters work.

Blackboard at the Laurent Schwartz Center for Mathematics, École Polytechnique.
This article contains special characters.
Without proper rendering support, you may see question marks, boxes, or other symbols.

The Unicode Standard encodes almost all standard characters used in mathematics.

Unicode Technical Report \#25 provides comprehensive information about the character repertoire, their properties, and guidelines for implementation.

Mathematical operators and symbols are in multiple Unicode blocks. Some of these blocks are dedicated to, or primarily contain, mathematical characters while others are a mix of mathematical and non-mathematical characters. This article covers all Unicode characters with a derived property of "Math".

\section{Dedicated blocks}

\ShowIndexing{}

\subsection{Mathematical Operators block}

Main article: Mathematical Operators (Unicode block)

The Mathematical Operators block (U+2200–U+22FF) contains characters for mathematical, logical, and set notation.

Mathematical Operators[1]

Official Unicode Consortium code chart (PDF)
=GFT
	 	0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+220x	∀	∁	∂	∃	∄	∅	∆	∇	∈	∉	∊	∋	∌	∍	∎	∏
U+221x	∐	∑	−	∓	∔	∕	∖	∗	∘	∙	√	∛	∜	∝	∞	∟
U+222x	∠	∡	∢	∣	∤	∥	∦	∧	∨	∩	∪	∫	∬	∭	∮	∯
U+223x	∰	∱	∲	∳	∴	∵	∶	∷	∸	∹	∺	∻	∼	∽	∾	∿
U+224x	≀	≁	≂	≃	≄	≅	≆	≇	≈	≉	≊	≋	≌	≍	≎	≏
U+225x	≐	≑	≒	≓	≔	≕	≖	≗	≘	≙	≚	≛	≜	≝	≞	≟
U+226x	≠	≡	≢	≣	≤	≥	≦	≧	≨	≩	≪	≫	≬	≭	≮	≯
U+227x	≰	≱	≲	≳	≴	≵	≶	≷	≸	≹	≺	≻	≼	≽	≾	≿
U+228x	⊀	⊁	⊂	⊃	⊄	⊅	⊆	⊇	⊈	⊉	⊊	⊋	⊌	⊍	⊎	⊏
U+229x	⊐	⊑	⊒	⊓	⊔	⊕	⊖	⊗	⊘	⊙	⊚	⊛	⊜	⊝	⊞	⊟
U+22Ax	⊠	⊡	⊢	⊣	⊤	⊥	⊦	⊧	⊨	⊩	⊪	⊫	⊬	⊭	⊮	⊯
U+22Bx	⊰	⊱	⊲	⊳	⊴	⊵	⊶	⊷	⊸	⊹	⊺	⊻	⊼	⊽	⊾	⊿
U+22Cx	⋀	⋁	⋂	⋃	⋄	⋅	⋆	⋇	⋈	⋉	⋊	⋋	⋌	⋍	⋎	⋏
U+22Dx	⋐	⋑	⋒	⋓	⋔	⋕	⋖	⋗	⋘	⋙	⋚	⋛	⋜	⋝	⋞	⋟
U+22Ex	⋠	⋡	⋢	⋣	⋤	⋥	⋦	⋧	⋨	⋩	⋪	⋫	⋬	⋭	⋮	⋯
U+22Fx	⋰	⋱	⋲	⋳	⋴	⋵	⋶	⋷	⋸	⋹	⋺	⋻	⋼	⋽	⋾	⋿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Supplemental Mathematical Operators block}

Main article: Supplemental Mathematical Operators (Unicode block)

The Supplemental Mathematical Operators block (U+2A00–U+2AFF) contains various mathematical symbols, including N-ary operators, summations and integrals, intersections and unions, logical and relational operators, and subset/superset relations.

Supplemental Mathematical Operators[1]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+2A0x	⨀	⨁	⨂	⨃	⨄	⨅	⨆	⨇	⨈	⨉	⨊	⨋	⨌	⨍	⨎	⨏
U+2A1x	⨐	⨑	⨒	⨓	⨔	⨕	⨖	⨗	⨘	⨙	⨚	⨛	⨜	⨝	⨞	⨟
U+2A2x	⨠	⨡	⨢	⨣	⨤	⨥	⨦	⨧	⨨	⨩	⨪	⨫	⨬	⨭	⨮	⨯
U+2A3x	⨰	⨱	⨲	⨳	⨴	⨵	⨶	⨷	⨸	⨹	⨺	⨻	PG	PF	⨾	⨿
U+2A4x	⩀	⩁	⩂	⩃	⩄	⩅	⩆	⩇	⩈	⩉	⩊	⩋	⩌	⩍	⩎	⩏
U+2A5x	⩐	⩑	⩒	⩓	⩔	⩕	⩖	⩗	⩘	⩙	⩚	⩛	⩜	⩝	⩞	⩟
U+2A6x	⩠	⩡	⩢	⩣	⩤	⩥	⩦	⩧	⩨	⩩	⩪	⩫	⩬	⩭	⩮	⩯
U+2A7x	⩰	⩱	⩲	⩳	⩴	⩵	⩶	⩷	⩸	⩹	⩺	⩻	⩼	⩽	⩾	⩿
U+2A8x	⪀	⪁	⪂	⪃	⪄	⪅	⪆	⪇	⪈	⪉	⪊	⪋	⪌	⪍	⪎	⪏
U+2A9x	⪐	⪑	⪒	⪓	⪔	⪕	⪖	⪗	⪘	⪙	⪚	⪛	⪜	⪝	⪞	⪟
U+2AAx	⪠	⪡	⪢	⪣	⪤	⪥	⪦	⪧	⪨	⪩	⪪	⪫	⪬	⪭	⪮	⪯
U+2ABx	⪰	⪱	⪲	⪳	⪴	⪵	⪶	⪷	⪸	⪹	⪺	⪻	⪼	⪽	⪾	⪿
U+2ACx	⫀	⫁	⫂	⫃	⫄	⫅	⫆	⫇	⫈	⫉	⫊	⫋	⫌	⫍	⫎	⫏
U+2ADx	⫐	⫑	⫒	⫓	⫔	⫕	⫖	⫗	⫘	⫙	⫚	⫛	⫝̸	⫝	⫞	⫟
U+2AEx	⫠	⫡	⫢	⫣	⫤	⫥	⫦	⫧	⫨	⫩	⫪	⫫	⫬	⫭	⫮	⫯
U+2AFx	⫰	⫱	⫲	⫳	⫴	⫵	⫶	⫷	⫸	⫹	⫺	⫻	⫼	⫽	⫾	⫿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Mathematical Alphanumeric Symbols block}

Main article: Mathematical Alphanumeric Symbols (Unicode block)

The Mathematical Alphanumeric Symbols block (U+1D400–U+1D7FF) contains Latin and Greek letters and decimal digits that enable mathematicians to denote different notions with different letter styles. The "holes" in the alphabetic ranges are filled by previously defined characters in the Letter like Symbols block shown below.

Mathematical Alphanumeric Symbols[1][2]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+1D40x	𝐀	𝐁	𝐂	𝐃	𝐄	𝐅	𝐆	𝐇	𝐈	𝐉	𝐊	𝐋	𝐌	𝐍	𝐎	𝐏
U+1D41x	𝐐	𝐑	𝐒	𝐓	𝐔	𝐕	𝐖	𝐗	𝐘	𝐙	𝐚	𝐛	𝐜	𝐝	𝐞	𝐟
U+1D42x	𝐠	𝐡	𝐢	𝐣	𝐤	𝐥	𝐦	𝐧	𝐨	𝐩	𝐪	𝐫	𝐬	𝐭	𝐮	𝐯
U+1D43x	𝐰	𝐱	𝐲	𝐳	𝐴	𝐵	𝐶	𝐷	𝐸	𝐹	𝐺	𝐻	𝐼	𝐽	𝐾	𝐿
U+1D44x	𝑀	𝑁	𝑂	𝑃	𝑄	𝑅	𝑆	𝑇	𝑈	𝑉	𝑊	𝑋	𝑌	𝑍	𝑎	𝑏
U+1D45x	𝑐	𝑑	𝑒	𝑓	𝑔		𝑖	𝑗	𝑘	𝑙	𝑚	𝑛	𝑜	𝑝	𝑞	𝑟
U+1D46x	𝑠	𝑡	𝑢	𝑣	𝑤	𝑥	𝑦	𝑧	𝑨	𝑩	𝑪	𝑫	𝑬	𝑭	𝑮	𝑯
U+1D47x	𝑰	𝑱	𝑲	𝑳	𝑴	𝑵	𝑶	𝑷	𝑸	𝑹	𝑺	𝑻	𝑼	𝑽	𝑾	𝑿
U+1D48x	𝒀	𝒁	𝒂	𝒃	𝒄	𝒅	𝒆	𝒇	𝒈	𝒉	𝒊	𝒋	𝒌	𝒍	𝒎	𝒏
U+1D49x	𝒐	𝒑	𝒒	𝒓	𝒔	𝒕	𝒖	𝒗	𝒘	𝒙	𝒚	𝒛	𝒜		𝒞	𝒟
U+1D4Ax			𝒢			𝒥	𝒦			𝒩	𝒪	𝒫	𝒬		𝒮	𝒯
U+1D4Bx	𝒰	𝒱	𝒲	𝒳	𝒴	𝒵	𝒶	𝒷	𝒸	𝒹		𝒻		𝒽	𝒾	𝒿
U+1D4Cx	𝓀	𝓁	𝓂	𝓃		𝓅	𝓆	𝓇	𝓈	𝓉	𝓊	𝓋	𝓌	𝓍	𝓎	𝓏
U+1D4Dx	𝓐	𝓑	𝓒	𝓓	𝓔	𝓕	𝓖	𝓗	𝓘	𝓙	𝓚	𝓛	𝓜	𝓝	𝓞	𝓟
U+1D4Ex	𝓠	𝓡	𝓢	𝓣	𝓤	𝓥	𝓦	𝓧	𝓨	𝓩	𝓪	𝓫	𝓬	𝓭	𝓮	𝓯
U+1D4Fx	𝓰	𝓱	𝓲	𝓳	𝓴	𝓵	𝓶	𝓷	𝓸	𝓹	𝓺	𝓻	𝓼	𝓽	𝓾	𝓿
U+1D50x	𝔀	𝔁	𝔂	𝔃	𝔄	𝔅		𝔇	𝔈	𝔉	𝔊			𝔍	𝔎	𝔏
U+1D51x	𝔐	𝔑	𝔒	𝔓	𝔔		𝔖	𝔗	𝔘	𝔙	𝔚	𝔛	𝔜		𝔞	𝔟
U+1D52x	𝔠	𝔡	𝔢	𝔣	𝔤	𝔥	𝔦	𝔧	𝔨	𝔩	𝔪	𝔫	𝔬	𝔭	𝔮	𝔯
U+1D53x	𝔰	𝔱	𝔲	𝔳	𝔴	𝔵	𝔶	𝔷	𝔸	𝔹		𝔻	𝔼	𝔽	𝔾	
U+1D54x	𝕀	𝕁	𝕂	𝕃	𝕄		𝕆				𝕊	𝕋	𝕌	𝕍	𝕎	𝕏
U+1D55x	𝕐		𝕒	𝕓	𝕔	𝕕	𝕖	𝕗	𝕘	𝕙	𝕚	𝕛	𝕜	𝕝	𝕞	𝕟
U+1D56x	𝕠	𝕡	𝕢	𝕣	𝕤	𝕥	𝕦	𝕧	𝕨	𝕩	𝕪	𝕫	𝕬	𝕭	𝕮	𝕯
U+1D57x	𝕰	𝕱	𝕲	𝕳	𝕴	𝕵	𝕶	𝕷	𝕸	𝕹	𝕺	𝕻	𝕼	𝕽	𝕾	𝕿
U+1D58x	𝖀	𝖁	𝖂	𝖃	𝖄	𝖅	𝖆	𝖇	𝖈	𝖉	𝖊	𝖋	𝖌	𝖍	𝖎	𝖏
U+1D59x	𝖐	𝖑	𝖒	𝖓	𝖔	𝖕	𝖖	𝖗	𝖘	𝖙	𝖚	𝖛	𝖜	𝖝	𝖞	𝖟
U+1D5Ax	𝖠	𝖡	𝖢	𝖣	𝖤	𝖥	𝖦	𝖧	𝖨	𝖩	𝖪	𝖫	𝖬	𝖭	𝖮	𝖯
U+1D5Bx	𝖰	𝖱	𝖲	𝖳	𝖴	𝖵	𝖶	𝖷	𝖸	𝖹	𝖺	𝖻	𝖼	𝖽	𝖾	𝖿
U+1D5Cx	𝗀	𝗁	𝗂	𝗃	𝗄	𝗅	𝗆	𝗇	𝗈	𝗉	𝗊	𝗋	𝗌	𝗍	𝗎	𝗏
U+1D5Dx	𝗐	𝗑	𝗒	𝗓	𝗔	𝗕	𝗖	𝗗	𝗘	𝗙	𝗚	𝗛	𝗜	𝗝	𝗞	𝗟
U+1D5Ex	𝗠	𝗡	𝗢	𝗣	𝗤	𝗥	𝗦	𝗧	𝗨	𝗩	𝗪	𝗫	𝗬	𝗭	𝗮	𝗯
U+1D5Fx	𝗰	𝗱	𝗲	𝗳	𝗴	𝗵	𝗶	𝗷	𝗸	𝗹	𝗺	𝗻	𝗼	𝗽	𝗾	𝗿
U+1D60x	𝘀	𝘁	𝘂	𝘃	𝘄	𝘅	𝘆	𝘇	𝘈	𝘉	𝘊	𝘋	𝘌	𝘍	𝘎	𝘏
U+1D61x	𝘐	𝘑	𝘒	𝘓	𝘔	𝘕	𝘖	𝘗	𝘘	𝘙	𝘚	𝘛	𝘜	𝘝	𝘞	𝘟
U+1D62x	𝘠	𝘡	𝘢	𝘣	𝘤	𝘥	𝘦	𝘧	𝘨	𝘩	𝘪	𝘫	𝘬	𝘭	𝘮	𝘯
U+1D63x	𝘰	𝘱	𝘲	𝘳	𝘴	𝘵	𝘶	𝘷	𝘸	𝘹	𝘺	𝘻	𝘼	𝘽	𝘾	𝘿
U+1D64x	𝙀	𝙁	𝙂	𝙃	𝙄	𝙅	𝙆	𝙇	𝙈	𝙉	𝙊	𝙋	𝙌	𝙍	𝙎	𝙏
U+1D65x	𝙐	𝙑	𝙒	𝙓	𝙔	𝙕	𝙖	𝙗	𝙘	𝙙	𝙚	𝙛	𝙜	𝙝	𝙞	𝙟
U+1D66x	𝙠	𝙡	𝙢	𝙣	𝙤	𝙥	𝙦	𝙧	𝙨	𝙩	𝙪	𝙫	𝙬	𝙭	𝙮	𝙯
U+1D67x	𝙰	𝙱	𝙲	𝙳	𝙴	𝙵	𝙶	𝙷	𝙸	𝙹	𝙺	𝙻	𝙼	𝙽	𝙾	𝙿
U+1D68x	𝚀	𝚁	𝚂	𝚃	𝚄	𝚅	𝚆	𝚇	𝚈	𝚉	𝚊	𝚋	𝚌	𝚍	𝚎	𝚏
U+1D69x	𝚐	𝚑	𝚒	𝚓	𝚔	𝚕	𝚖	𝚗	𝚘	𝚙	𝚚	𝚛	𝚜	𝚝	𝚞	𝚟
U+1D6Ax	𝚠	𝚡	𝚢	𝚣	𝚤	𝚥			𝚨	𝚩	𝚪	𝚫	𝚬	𝚭	𝚮	𝚯
U+1D6Bx	𝚰	𝚱	𝚲	𝚳	𝚴	𝚵	𝚶	𝚷	𝚸	𝚹	𝚺	𝚻	𝚼	𝚽	𝚾	𝚿
U+1D6Cx	𝛀	𝛁	𝛂	𝛃	𝛄	𝛅	𝛆	𝛇	𝛈	𝛉	𝛊	𝛋	𝛌	𝛍	𝛎	𝛏
U+1D6Dx	𝛐	𝛑	𝛒	𝛓	𝛔	𝛕	𝛖	𝛗	𝛘	𝛙	𝛚	𝛛	𝛜	𝛝	𝛞	𝛟
U+1D6Ex	𝛠	𝛡	𝛢	𝛣	𝛤	𝛥	𝛦	𝛧	𝛨	𝛩	𝛪	𝛫	𝛬	𝛭	𝛮	𝛯
U+1D6Fx	𝛰	𝛱	𝛲	𝛳	𝛴	𝛵	𝛶	𝛷	𝛸	𝛹	𝛺	𝛻	𝛼	𝛽	𝛾	𝛿
U+1D70x	𝜀	𝜁	𝜂	𝜃	𝜄	𝜅	𝜆	𝜇	𝜈	𝜉	𝜊	𝜋	𝜌	𝜍	𝜎	𝜏
U+1D71x	𝜐	𝜑	𝜒	𝜓	𝜔	𝜕	𝜖	𝜗	𝜘	𝜙	𝜚	𝜛	𝜜	𝜝	𝜞	𝜟
U+1D72x	𝜠	𝜡	𝜢	𝜣	𝜤	𝜥	𝜦	𝜧	𝜨	𝜩	𝜪	𝜫	𝜬	𝜭	𝜮	𝜯
U+1D73x	𝜰	𝜱	𝜲	𝜳	𝜴	𝜵	𝜶	𝜷	𝜸	𝜹	𝜺	𝜻	𝜼	𝜽	𝜾	𝜿
U+1D74x	𝝀	𝝁	𝝂	𝝃	𝝄	𝝅	𝝆	𝝇	𝝈	𝝉	𝝊	𝝋	𝝌	𝝍	𝝎	𝝏
U+1D75x	𝝐	𝝑	𝝒	𝝓	𝝔	𝝕	𝝖	𝝗	𝝘	𝝙	𝝚	𝝛	𝝜	𝝝	𝝞	𝝟
U+1D76x	𝝠	𝝡	𝝢	𝝣	𝝤	𝝥	𝝦	𝝧	𝝨	𝝩	𝝪	𝝫	𝝬	𝝭	𝝮	𝝯
U+1D77x	𝝰	𝝱	𝝲	𝝳	𝝴	𝝵	𝝶	𝝷	𝝸	𝝹	𝝺	𝝻	𝝼	𝝽	𝝾	𝝿
U+1D78x	𝞀	𝞁	𝞂	𝞃	𝞄	𝞅	𝞆	𝞇	𝞈	𝞉	𝞊	𝞋	𝞌	𝞍	𝞎	𝞏
U+1D79x	𝞐	𝞑	𝞒	𝞓	𝞔	𝞕	𝞖	𝞗	𝞘	𝞙	𝞚	𝞛	𝞜	𝞝	𝞞	𝞟
U+1D7Ax	𝞠	𝞡	𝞢	𝞣	𝞤	𝞥	𝞦	𝞧	𝞨	𝞩	𝞪	𝞫	𝞬	𝞭	𝞮	𝞯
U+1D7Bx	𝞰	𝞱	𝞲	𝞳	𝞴	𝞵	𝞶	𝞷	𝞸	𝞹	𝞺	𝞻	𝞼	𝞽	𝞾	𝞿
U+1D7Cx	𝟀	𝟁	𝟂	𝟃	𝟄	𝟅	𝟆	𝟇	𝟈	𝟉	𝟊	𝟋			𝟎	𝟏
U+1D7Dx	𝟐	𝟑	𝟒	𝟓	𝟔	𝟕	𝟖	𝟗	𝟘	𝟙	𝟚	𝟛	𝟜	𝟝	𝟞	𝟟
U+1D7Ex	𝟠	𝟡	𝟢	𝟣	𝟤	𝟥	𝟦	𝟧	𝟨	𝟩	𝟪	𝟫	𝟬	𝟭	𝟮	𝟯
U+1D7Fx	𝟰	𝟱	𝟲	𝟳	𝟴	𝟵	𝟶	𝟷	𝟸	𝟹	𝟺	𝟻	𝟼	𝟽	𝟾	𝟿
=TEX
Notes

1. As of Unicode version 12.0

2. Grey areas indicate non-assigned code points

\subsection{Letterlike Symbols block}

Main article: Letterlike Symbols (Unicode block)

The Letterlike Symbols block (U+2100–U+214F) includes variables. Most alphabetic math symbols are in the Mathematical Alphanumeric Symbols block shown above.

The math subset of this block is U+2102, U+2107, U+210A–U+2113, U+2115, U+2118–U+2119, U+2124, U+2128–U+2129, U+212C, U+212F, U+2133, U+2135, U+213C–U+2149, and U+214B.

Letterlike Symbols[1] 

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+210x	℀	℁	ℂ	℃	℄	℅	℆	ℇ	℈	℉	ℊ	ℋ	ℌ	ℍ	ℎ	ℏ
U+211x	ℐ	ℑ	ℒ	ℓ	℔	ℕ	№	℗	℘	ℙ	ℚ	ℛ	ℜ	ℝ	℞	℟
U+212x	℠	℡	™	℣	ℤ	℥	Ω	℧	ℨ	℩	K	Å	ℬ	ℭ	℮	ℯ
U+213x	ℰ	ℱ	Ⅎ	ℳ	ℴ	ℵ	ℶ	ℷ	ℸ	ℹ	℺	℻	ℼ	ℽ	ℾ	ℿ
U+214x	⅀	⅁	⅂	⅃	⅄	ⅅ	ⅆ	ⅇ	ⅈ	ⅉ	⅊	⅋	⅌	⅍	ⅎ	⅏
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Miscellaneous Mathematical Symbols-A block}

Main article: Miscellaneous Mathematical Symbols-A (Unicode block)
The Miscellaneous Mathematical Symbols-A block (U+27C0–U+27EF) contains characters for mathematical, logical, and database notation.

Miscellaneous Mathematical Symbols-A[1]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+27Cx	⟀	⟁	⟂	⟃	⟄	⟅	⟆	⟇	⟈	⟉	⟊	⟋	⟌	⟍	⟎	⟏
U+27Dx	⟐	⟑	⟒	⟓	⟔	⟕	⟖	⟗	⟘	⟙	⟚	⟛	⟜	⟝	⟞	⟟
U+27Ex	⟠	⟡	⟢	⟣	⟤	⟥	⟦	⟧	⟨	⟩	⟪	⟫	⟬	⟭	⟮	⟯
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Miscellaneous Mathematical Symbols-B block}

Main article: Miscellaneous Mathematical Symbols-B (Unicode block)

The Miscellaneous Mathematical Symbols-B block (U+2980–U+29FF) contains miscellaneous mathematical symbols, including brackets, angles, and circle symbols.

Miscellaneous Mathematical Symbols-B[1]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+298x	⦀	⦁	⦂	⦃	⦄	⦅	⦆	⦇	⦈	⦉	⦊	⦋	⦌	⦍	⦎	⦏
U+299x	⦐	⦑	⦒	⦓	⦔	⦕	⦖	⦗	⦘	⦙	⦚	⦛	⦜	⦝	⦞	⦟
U+29Ax	⦠	⦡	⦢	⦣	⦤	⦥	⦦	⦧	⦨	⦩	⦪	⦫	⦬	⦭	⦮	⦯
U+29Bx	⦰	⦱	⦲	⦳	⦴	⦵	⦶	⦷	⦸	⦹	⦺	⦻	⦼	⦽	⦾	⦿
U+29Cx	⧀	⧁	⧂	⧃	⧄	⧅	⧆	⧇	⧈	⧉	⧊	⧋	⧌	⧍	⧎	⧏
U+29Dx	⧐	⧑	⧒	⧓	⧔	⧕	⧖	⧗	⧘	⧙	⧚	⧛	⧜	⧝	⧞	⧟
U+29Ex	⧠	⧡	⧢	⧣	⧤	⧥	⧦	⧧	⧨	⧩	⧪	⧫	⧬	⧭	⧮	⧯
U+29Fx	⧰	⧱	⧲	⧳	⧴	⧵	⧶	⧷	⧸	⧹	⧺	⧻	⧼	⧽	⧾	⧿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Miscellaneous Technical block}

Main article: Miscellaneous Technical (Unicode block)
The Miscellaneous Technical block (U+2300–U+23FF) includes braces and operators.

The math subset of this block is U+2308–U+230B, U+2320-U+2321, U+237C, U+239B-U+23B5, 23B7, U+23D0, and U+23DC-U+23E2.

Miscellaneous Technical[1][2]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+230x	⌀	⌁	⌂	⌃	⌄	⌅	⌆	⌇	⌈	⌉	⌊	⌋	⌌	⌍	⌎	⌏
U+231x	⌐	⌑	⌒	⌓	⌔	⌕	⌖	⌗	⌘	⌙	⌚	⌛	⌜	⌝	⌞	⌟
U+232x	⌠	⌡	⌢	⌣	⌤	⌥	⌦	⌧	⌨	〈	〉	⌫	⌬	⌭	⌮	⌯
U+233x	⌰	⌱	⌲	⌳	⌴	⌵	⌶	⌷	⌸	⌹	⌺	⌻	⌼	⌽	⌾	⌿
U+234x	⍀	⍁	⍂	⍃	⍄	⍅	⍆	⍇	⍈	⍉	⍊	⍋	⍌	⍍	⍎	⍏
U+235x	⍐	⍑	⍒	⍓	⍔	⍕	⍖	⍗	⍘	⍙	⍚	⍛	⍜	⍝	⍞	⍟
U+236x	⍠	⍡	⍢	⍣	⍤	⍥	⍦	⍧	⍨	⍩	⍪	⍫	⍬	⍭	⍮	⍯
U+237x	⍰	⍱	⍲	⍳	⍴	⍵	⍶	⍷	⍸	⍹	⍺	⍻	⍼	⍽	⍾	⍿
U+238x	⎀	⎁	⎂	⎃	⎄	⎅	⎆	⎇	⎈	⎉	⎊	⎋	⎌	⎍	⎎	⎏
U+239x	⎐	⎑	⎒	⎓	⎔	⎕	⎖	⎗	⎘	⎙	⎚	⎛	⎜	⎝	⎞	⎟
U+23Ax	⎠	⎡	⎢	⎣	⎤	⎥	⎦	⎧	⎨	⎩	⎪	⎫	⎬	⎭	⎮	⎯
U+23Bx	⎰	⎱	⎲	⎳	⎴	⎵	⎶	⎷	⎸	⎹	⎺	⎻	⎼	⎽	⎾	⎿
U+23Cx	⏀	⏁	⏂	⏃	⏄	⏅	⏆	⏇	⏈	⏉	⏊	⏋	⏌	⏍	⏎	⏏
U+23Dx	⏐	⏑	⏒	⏓	⏔	⏕	⏖	⏗	⏘	⏙	⏚	⏛	⏜	⏝	⏞	⏟
U+23Ex	⏠	⏡	⏢	⏣	⏤	⏥	⏦	⏧	⏨	⏩	⏪	⏫	⏬	⏭	⏮	⏯
U+23Fx	⏰	⏱	⏲	⏳	⏴	⏵	⏶	⏷	⏸	⏹	⏺	⏻
=TEX
Notes

1. As of Unicode version 12.0

2. Unicode code points U+2329 and U+232A are deprecated as of Unicode version 5.2

\subsection{Geometric Shapes block}

Main article: Geometric Shapes (Unicode block)

The Geometric Shapes block (U+25A0–U+25FF) contains geometric shape symbols.

The math subset of this block is U+25A0–25A1, U+25AE–25B7, U+25BC–25C1, U+25C6–25C7, U+25CA–25CB, U+25CF–25D3, U+25E2, U+25E4, U+25E7–25EC, and U+25F8–25FF.

Geometric Shapes[1]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+25Ax	■	□	▢	▣	▤	▥	▦	▧	▨	▩	▪	▫	▬	▭	▮	▯
U+25Bx	▰	▱	▲	△	▴	▵	▶	▷	▸	▹	►	▻	▼	▽	▾	▿
U+25Cx	◀	◁	◂	◃	◄	◅	◆	◇	◈	◉	◊	○	◌	◍	◎	●
U+25Dx	◐	◑	◒	◓	◔	◕	◖	◗	◘	◙	◚	◛	◜	◝	◞	◟
U+25Ex	◠	◡	◢	◣	◤	◥	◦	◧	◨	◩	◪	◫	◬	◭	◮	◯
U+25Fx	◰	◱	◲	◳	◴	◵	◶	◷	◸	◹	◺	◻	◼	◽	◾	◿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Miscellaneous Symbols and Arrows block}

Main article: Miscellaneous Symbols and Arrows (Unicode block)

The Miscellaneous Symbols and Arrows block (U+2B00–U+2BFF Arrows) contains arrows and geometric shapes with various fills.

The math subset of this block is U+2B30–2B44 and U+2B47–2B4C.

Miscellaneous Symbols and Arrows[1][2]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+2B0x	⬀	⬁	⬂	⬃	⬄	⬅	⬆	⬇	⬈	⬉	⬊	⬋	⬌	⬍	⬎	⬏
U+2B1x	⬐	⬑	⬒	⬓	⬔	⬕	⬖	⬗	⬘	⬙	⬚	⬛	⬜	⬝	⬞	⬟
U+2B2x	⬠	⬡	⬢	⬣	⬤	⬥	⬦	⬧	⬨	⬩	⬪	⬫	⬬	⬭	⬮	⬯
U+2B3x	⬰	⬱	⬲	⬳	⬴	⬵	⬶	⬷	⬸	⬹	⬺	⬻	⬼	⬽	⬾	⬿
U+2B4x	⭀	⭁	⭂	⭃	⭄	⭅	⭆	⭇	⭈	⭉	⭊	⭋	⭌	⭍	⭎	⭏
U+2B5x	⭐	⭑	⭒	⭓	⭔	⭕	⭖	⭗	⭘	⭙	⭚	⭛	⭜	⭝	⭞	⭟
U+2B6x	⭠	⭡	⭢	⭣	⭤	⭥	⭦	⭧	⭨	⭩	⭪	⭫	⭬	⭭	⭮	⭯
U+2B7x	⭰	⭱	⭲	⭳			⭶	⭷	⭸	⭹	⭺	⭻	⭼	⭽	⭾	⭿
U+2B8x	⮀	⮁	⮂	⮃	⮄	⮅	⮆	⮇	⮈	⮉	⮊	⮋	⮌	⮍	⮎	⮏
U+2B9x	⮐	⮑	⮒	⮓	⮔	⮕			⮘	⮙	⮚	⮛	⮜	⮝	⮞	⮟
U+2BAx	⮠	⮡	⮢	⮣	⮤	⮥	⮦	⮧	⮨	⮩	⮪	⮫	⮬	⮭	⮮	⮯
U+2BBx	⮰	⮱	⮲	⮳	⮴	⮵	⮶	⮷	⮸	⮹	⮺	⮻	⮼	⮽	⮾	⮿
U+2BCx	⯀	⯁	⯂	⯃	⯄	⯅	⯆	⯇	⯈	⯉	⯊	⯋	⯌	⯍	⯎	⯏
U+2BDx	⯐	⯑	⯒	⯓	⯔	⯕	⯖	⯗	⯘	⯙	⯚	⯛	⯜	⯝	⯞	⯟
U+2BEx	⯠	⯡	⯢	⯣	⯤	⯥	⯦	⯧	⯨	⯩	⯪	⯫	⯬	⯭	⯮	⯯
U+2BFx	⯰	⯱	⯲	⯳	⯴	⯵	⯶	⯷	⯸	⯹	⯺	⯻
=TEX
Notes

1. As of Unicode version 12.0

2. Grey areas indicate non-assigned code points

\subsection{Arrows block}

Main article: Arrows (Unicode block)

The Arrows block (U+2190–U+21FF) contains line, curve, and semicircle arrows and arrow-like operators.

Arrows[1]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+219x	←	↑	→	↓	↔	OK	↖	OH	OI	↙	↚	↛	↜	↝	↞	↟
U+21Ax	↠	↡	↢	↣	↤	↥	↦	↧	↨	↩	↪	↫	↬	↭	↮	↯
U+21Bx	↰	↱	↲	↳	↴	↵	↶	↷	↸	↹	↺	↻	↼	↽	↾	↿
U+21Cx	⇀	⇁	⇂	⇃	⇄	⇅	⇆	⇇	⇈	⇉	⇊	⇋	⇌	⇍	⇎	⇏
U+21Dx	⇐	⇑	⇒	⇓	⇔	⇕	⇖	⇗	⇘	⇙	⇚	⇛	⇜	⇝	⇞	⇟
U+21Ex	⇠	⇡	⇢	⇣	⇤	⇥	⇦	⇧	⇨	⇩	⇪	⇫	⇬	⇭	⇮	⇯
U+21Fx	⇰	⇱	⇲	⇳	⇴	⇵	⇶	⇷	⇸	⇹	⇺	⇻	⇼	⇽	⇾	⇿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Supplemental Arrows-A block}

Main article: Supplemental Arrows-A (Unicode block)
The Supplemental Arrows-A block (U+27F0–U+27FF) contains arrows and arrow-like operators.

Supplemental Arrows-A[1]

Official Unicode Consortium code chart (PDF)
=GFT
		 0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+27Fx	⟰	⟱	⟲	⟳	⟴	⟵	⟶	⟷	⟸	⟹	⟺	⟻	⟼	⟽	⟾	⟿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Supplemental Arrows-B block}

Main article: Supplemental Arrows-B (Unicode block)

The Supplemental Arrows-B block (U+2900–U+297F) contains arrows and arrow-like operators (arrow tails, crossing arrows, curved arrows, and harpoons).

Supplemental Arrows-B[1]

Official Unicode Consortium code chart (PDF)
=GFT
		 0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+290x	⤀	⤁	⤂	⤃	⤄	⤅	⤆	⤇	⤈	⤉	⤊	⤋	⤌	⤍	⤎	⤏
U+291x	⤐	⤑	⤒	⤓	⤔	⤕	⤖	⤗	⤘	⤙	⤚	⤛	⤜	⤝	⤞	⤟
U+292x	⤠	⤡	⤢	⤣	⤤	⤥	⤦	⤧	⤨	⤩	⤪	⤫	⤬	⤭	⤮	⤯
U+293x	⤰	⤱	⤲	⤳	⤴	⤵	⤶	⤷	⤸	⤹	⤺	⤻	⤼	⤽	⤾	⤿
U+294x	⥀	⥁	⥂	⥃	⥄	⥅	⥆	⥇	⥈	⥉	⥊	⥋	⥌	⥍	⥎	⥏
U+295x	⥐	⥑	⥒	⥓	⥔	⥕	⥖	⥗	⥘	⥙	⥚	⥛	⥜	⥝	⥞	⥟
U+296x	⥠	⥡	⥢	⥣	⥤	⥥	⥦	⥧	⥨	⥩	⥪	⥫	⥬	⥭	⥮	⥯
U+297x	⥰	⥱	⥲	⥳	⥴	⥵	⥶	⥷	⥸	⥹	⥺	⥻	⥼	⥽	⥾	⥿
=TEX
Notes

1. As of Unicode version 12.0

\subsection{Combining Diacritical Marks for Symbols block}

Main article: Combining Diacritical Marks for Symbols (Unicode block)

The Combining Diacritical Marks for Symbols block contains arrows, dots, enclosures, and overlays for modifying symbol characters.

The math subset of this block is U+20D0–U+20DC, U+20E1, U+20E5–U+20E6, and U+20EB–U+20EF.

Combining Diacritical Marks for Symbols[1][2]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+20Dx	◌⃐	◌⃑	◌⃒	◌⃓	◌⃔	◌⃕	◌⃖	◌⃗	◌⃘	◌⃙	◌⃚	◌⃛	◌⃜	◌⃝	◌⃞	◌⃟
U+20Ex	◌⃠	◌⃡	◌⃢	◌⃣	◌⃤	◌⃥	◌⃦	◌⃧	◌⃨	◌⃩	◌⃪	◌⃫	◌⃬	◌⃭	◌⃮	◌⃯
U+20Fx	◌⃰
=TEX
Notes


1. As of Unicode version 12.0

2. Grey areas indicate non-assigned code points

\subsection{Arabic Mathematical Alphabetic Symbols block}

Main article: Arabic Mathematical Alphabetic Symbols block

The Arabic Mathematical Alphabetic Symbols block (U+1EE00–U+1EEFF) contains characters used in Arabic mathematical expressions.

Arabic Mathematical Alphabetic Symbols[1][2]

Official Unicode Consortium code chart (PDF)
=GFT
		0	1	2	3	4	5	6	7	8	9	A	B	C	D	E	F
U+1EE0x	𞸀	𞸁	𞸂	𞸃		𞸅	𞸆	𞸇	𞸈	𞸉	𞸊	𞸋	𞸌	𞸍	𞸎	𞸏
U+1EE1x	𞸐	𞸑	𞸒	𞸓	𞸔	𞸕	𞸖	𞸗	𞸘	𞸙	𞸚	𞸛	𞸜	𞸝	𞸞	𞸟
U+1EE2x		𞸡	𞸢		𞸤			𞸧		𞸩	𞸪	𞸫	𞸬	𞸭	𞸮	𞸯
U+1EE3x	𞸰	𞸱	𞸲		𞸴	𞸵	𞸶	𞸷		𞸹		𞸻				
U+1EE4x			𞹂					𞹇		𞹉		𞹋		𞹍	𞹎	𞹏
U+1EE5x		𞹑	𞹒		𞹔			𞹗		𞹙		𞹛		𞹝		𞹟
U+1EE6x		𞹡	𞹢		𞹤			𞹧	𞹨	𞹩	𞹪		𞹬	𞹭	𞹮	𞹯
U+1EE7x	𞹰	𞹱	𞹲		𞹴	𞹵	𞹶	𞹷		𞹹	𞹺	𞹻	𞹼		𞹾	
U+1EE8x	𞺀	𞺁	𞺂	𞺃	𞺄	𞺅	𞺆	𞺇	𞺈	𞺉		𞺋	𞺌	𞺍	𞺎	𞺏
U+1EE9x	𞺐	𞺑	𞺒	𞺓	𞺔	𞺕	𞺖	𞺗	𞺘	𞺙	𞺚	𞺛				
U+1EEAx		𞺡	𞺢	𞺣		𞺥	𞺦	𞺧	𞺨	𞺩		𞺫	𞺬	𞺭	𞺮	𞺯
U+1EEBx	𞺰	𞺱	𞺲	𞺳	𞺴	𞺵	𞺶	𞺷	𞺸	𞺹	𞺺	𞺻				
U+1EECx																
U+1EEDx																
U+1EEEx																
U+1EEFx	𞻰	𞻱
=TEX
Notes

1. As of Unicode version 12.0

2. Grey areas indicate non-assigned code points

\subsection{Characters in other blocks}

Mathematical characters also appear in other blocks. Below is a list of these characters as of Unicode version 12.0:

Basic Latin block
=GFT
U+002B	+	PLUS SIGN
U+002D	-	HYPHEN-MINUS
U+003C	<	LESS-THAN SIGN
U+003D	=	EQUALS SIGN
U+003E	>	GREATER-THAN SIGN
U+005E	^	CIRCUMFLEX ACCENT
U+007C	|	VERTICAL LINE
U+007E	~	TILDE
=TEX
Latin-1 Supplement block
=GFT
U+00AC	¬	NOT SIGN
U+00B1	±	PLUS-MINUS SIGN
U+00D7	×	MULTIPLICATION SIGN
U+00F7	÷	DIVISION SIGN
=TEX
Greek and Coptic block
=GFT
U+03D0	ϐ	GREEK BETA SYMBOL
U+03D1	ϑ	GREEK THETA SYMBOL
U+03D2	ϒ	GREEK UPSILON WITH HOOK SYMBOL
U+03D5	ϕ	GREEK PHI SYMBOL
U+03F0	ϰ	GREEK KAPPA SYMBOL
U+03F1	ϱ	GREEK RHO SYMBOL
U+03F4	ϴ	GREEK CAPITAL THETA SYMBOL
U+03F5	ϵ	GREEK LUNATE EPSILON SYMBOL
U+03F6	϶	GREEK REVERSED LUNATE EPSILON SYMBOL
=TEX
Arabic block
=GFT
U+0606	؆	ARABIC-INDIC CUBE ROOT
U+0607	؇	ARABIC-INDIC FOURTH ROOT
U+0608	؈	ARABIC RAY
=TEX
General Punctuation block
=GFT
U+2016	‖	DOUBLE VERTICAL LINE
U+2032	′	PRIME
U+2033	″	DOUBLE PRIME
U+2034	‴	TRIPLE PRIME
U+2040	⁀	CHARACTER TIE
U+2044	⁄	FRACTION SLASH
U+2052	⁒	COMMERCIAL MINUS SIGN
U+2061	note	FUNCTION APPLICATION
U+2062	note	INVISIBLE TIMES
U+2063	note	INVISIBLE SEPARATOR
U+2064	note	INVISIBLE PLUS
=TEX
Note: non-marking character

Superscripts and Subscripts block
=GFT
U+207A	⁺	SUPERSCRIPT PLUS SIGN
U+207B	⁻	SUPERSCRIPT MINUS
U+207C	⁼	SUPERSCRIPT EQUALS SIGN
U+207D	⁽	SUPERSCRIPT LEFT PARENTHESIS
U+207E	⁾	SUPERSCRIPT RIGHT PARENTHESIS
U+208A	₊	SUBSCRIPT PLUS SIGN
U+208B	₋	SUBSCRIPT MINUS
U+208C	₌	SUBSCRIPT EQUALS SIGN
U+208D	₍	SUBSCRIPT LEFT PARENTHESIS
U+208E	₎	SUBSCRIPT RIGHT PARENTHESIS
=TEX
Miscellaneous Symbols block
=GFT
U+2605	★	BLACK STAR
U+2606	☆	WHITE STAR
U+2640	♀	FEMALE SIGN
U+2642	♂	MALE SIGN
U+2660	♠	BLACK SPADE SUIT
U+2661	♡	WHITE HEART SUIT
U+2662	♢	WHITE DIAMOND SUIT
U+2663	♣	BLACK CLUB SUIT
U+266D	♭	MUSIC FLAT SIGN
U+266E	♮	MUSIC NATURAL SIGN
U+266F	♯	MUSIC SHARP SIGN
=TEX
Alphabetic Presentation Forms block
=GFT
U+FB29	﬩	HEBREW LETTER ALTERNATIVE PLUS SIGN
=TEX
Small Form Variants block
=GFT
U+FE61	﹡	SMALL ASTERISK
U+FE62	﹢	SMALL PLUS SIGN
U+FE63	﹣	SMALL HYPHEN-MINUS
U+FE64	﹤	SMALL LESS-THAN SIGN
U+FE65	﹥	SMALL GREATER-THAN SIGN
U+FE66	﹦	SMALL EQUALS SIGN
U+FE68	﹨	SMALL REVERSE SOLIDUS
=TEX
Halfwidth and Fullwidth Forms block
=GFT
U+FF0B	＋	FULLWIDTH PLUS SIGN
U+FF1C	＜	FULLWIDTH LESS-THAN SIGN
U+FF1D	＝	FULLWIDTH EQUALS SIGN
U+FF1E	＞	FULLWIDTH GREATER-THAN SIGN
U+FF3C	＼	FULLWIDTH REVERSE SOLIDUS
U+FF3E	＾	FULLWIDTH CIRCUMFLEX ACCENT
U+FF5C	｜	FULLWIDTH VERTICAL LINE
U+FF5E	～	FULLWIDTH TILDE
U+FFE2	￢	FULLWIDTH NOT SIGN
U+FFE9	￩	HALFWIDTH LEFTWARDS ARROW
U+FFEA	￪	HALFWIDTH UPWARDS ARROW
U+FFEB	￫	HALFWIDTH RIGHTWARDS ARROW
U+FFEC	￬	HALFWIDTH DOWNWARDS ARROW
=TEX
See also
=GFT
List of mathematical symbols
List of logic symbols
Greek letters used in mathematics, science, and engineering
List of letters used in mathematics and science
Latin letters used in mathematics
Unicode subscripts and superscripts
Unicode symbols
CJK Compatibility Unicode symbols includes symbols for SI units
Units for order of magnitude shows position of SI units
References
 "Unicode Technical Report \#25: Unicode Support for Mathematics" (PDF). The Unicode Consortium. 2 April 2012. Retrieved 14 August 2014.
 "Unicode Character Database: Derived Core Properties". The Unicode Consortium. 19 February 2014. Retrieved 14 August 2014.
 "Unicode Technical Annex #44: Unicode Character Database" (PDF). The Unicode Consortium. 25 September 2013. Retrieved 14 August 2014.
External links
Mathematical Markup Language (MathML) W3C Recommendation. 3.0 (2nd ed.). W3C. 10 April 2014.
Images of glyphs in section 6.3.3 of the Mathematical Markup Language (MathML) W3C Recommendation. 2.0 (2nd ed.). W3C. 21 February 2001.

=TEX
% $Id: t055z.tex $

\section{Postscript}\label{POSTSCRIPT}


\pagebreak

%\section*{Bibliography}\label{BIBLIOGRAPHY}
%\addcontentsline{toc}{section}{Bibliography}

%{\def\section*#1{\ignore{#1}}
%\raggedright
%\bibliographystyle{rbjfmu}
%\bibliography{rbj,fmu}
%} %\raggedright

{\twocolumn[\section*{Index}\label{INDEX}]
\addcontentsline{toc}{section}{Index}
{\small\printindex}}

\end{document}
