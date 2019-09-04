grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

imports silver:langutil; 
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

imports edu:umn:cs:melt:exts:ableC:templateAlgebraicDataTypes:datatype:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:datatype:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:unification:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:templating:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:string:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:closure:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:constructor:abstractsyntax;

global builtin::Location = builtinLoc("prolog");
