#!/usr/bin/perl -w
# for extracting titles and abstracts from a collection of LaTeX
# documents and creating a list of abstracts in tex.

# parameters: input files names
# output to standard output.

# use XLogic::xpptran;

#$true=1;
#$false=0;

$title=""; $abstract=""; $bibref="";

print "\\section{Abstracts}\n";

while (<ARGV>) {
    if (/(pdftitle=|title)\{([^}]*)\}/) {if($title eq "") {$title=$2}}
    elsif (/bibref\{([^}]*)\}/) {$bibref=$1}
    elsif (/\\begin\{abstract\}/) {
	$abstract="";
	$_=<ARGV>;
	until (/\\end\{abstract\}/) {s/^\%(.*)$/$1/; $abstract.=$_; $_=<ARGV>};
	print "\\subsection{$title}";
	print "\n\n$abstract";
	if ($bibref) {print "\\cite{$bibref}"};
	print "\n";
        $title=""; $abstract=""; $bibref="";
    };
};
