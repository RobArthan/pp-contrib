********************************************************************************
* 
* rbj: some experiments with ProofPower.
* 
* Use the make file rbj.mkf  to process the document files.
* For instructions on how to do this type:
* 
* 	make -f rbj.mkf
* 
* and you will be given some basic help on using the make file.
*
* Copyright (c) 2004-2006 Roger Bishop Jones.
* 
* This file is supplied under the GNU General Public Licence (GPL) version 2.
* 
* For the terms of the GPL visit the OpenSource web site at http://www.opensource.org/
* 
* Contact: Roger Bishop Jones < rbj01@rbjones.com >
* 
********************************************************************************

The makefile enables the supplied materials to be used to re-run the
construction of a ProofPower database containing the theories
developed in the documents.  This consists primarily in the syntax and
type checking of specifications and the generation and checking of
proofs of various theorems.  The makefile can also be used to convert
the ProofPower LaTeX source documents to PDF documents.

You will need to have certain other items of software in place for
this to work.

1    ProofPower
2    Rob Arthan's "maths_egs" 

     (both obtainable from www.lemma1.com)

If you have a working ProofPower installation (and have set up your
environment variables appropriately) and have built the
"maths_eqs" database and put it in the ProofPower db directory
that should be OK for this build.

In addition, it will be necessary for the directory in which you
propose to run the build to be specified on your PATH variable and
included in the various LaTeX related paths (which normaly include
".").
It will also be necessary to have an INDEXSTYLE variable with the
build directory mentioned in it.

If these instructions should prove inadequate I would appreciate some feedback.
