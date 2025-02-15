/*

  $Id: sc_lex.l 1647 2016-07-01 11:57:57Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of Linear/C3 Library.

  Linear/C3 Library is free software: you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  Linear/C3 Library is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with Linear/C3 Library.  If not, see <http://www.gnu.org/licenses/>.

*/

%option nounput
%START COMMENT TEXT
%{
/*
	Grammaire lex necessaire pour l'analyse lexicale d'un systeme
	d'assertions. Les tokens renvoyes sont commentes dans le fichier
	"sc_gram.y".
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h> /* flex uses isatty */

#include "boolean.h"
#include "arithmetique.h"
#include "vecteur.h"

#include "sc_gram.h"

#define RETURN(x) /* fprintf(stderr, "lex: %d\n", x); */ return x

char * sc_internal_symbol_table(char *);
extern int syst_error(char *);

%}

%%
<TEXT>"VAR"			{ RETURN(VAR); }
<TEXT>[.A-Za-z_]['A-Za-z0-9_:#.]* { syst_lval.Variable = (Variable) sc_internal_symbol_table(syst_text); /*'*/
                                  RETURN(IDENT); }
<TEXT>\'[A-Za-z0-9_:#?. ]*\' { syst_lval.Variable = (Variable) sc_internal_symbol_table(syst_text); /*'*/
                                  RETURN(IDENT); }
<TEXT>[0-9]*[.DEe][0-9DEe\-]* { syst_lval.Variable = (Variable) sc_internal_symbol_table(syst_text); /*'*/
                                  RETURN(IDENT); }
<TEXT>[0-9]*			{ sscan_Value(syst_text,&syst_lval.Value);
                                  RETURN(CONSTANTE); }
<TEXT>"=="			{ RETURN(EGAL); }
<TEXT>"="			{ RETURN(EGAL); }
<TEXT>","			{ RETURN(VIRG); }
<TEXT>"+"			{ RETURN(PLUS); }
<TEXT>"-"			{ RETURN(MOINS); }
<TEXT>">"			{ RETURN(SUP); }
<TEXT>">="			{ RETURN(SUPEGAL); }
<TEXT>"<"			{ RETURN(INF); }
<TEXT>"<="			{ RETURN(INFEGAL); }
<TEXT>"{"			{ RETURN(ACCOUVR); }
<TEXT>"}"			{ RETURN(ACCFERM); }
<TEXT>[ \t\r\n]*		;
<TEXT>"#"                       {BEGIN COMMENT;}
<COMMENT>\n                     {BEGIN TEXT;}
<COMMENT>[^\n]*         ;
.             { syst_error("unexpected character"); }
%%

#define SYMBOLS_SIZE (10)

char * sc_internal_symbol_table(char * name)
{
  static int size = 0;
  static int index = 0; /* next available chunk */
  static char ** symbols = NULL;

  int i;

  if (index==size) {
    size += SYMBOLS_SIZE;
    if (symbols) symbols = (char**) realloc(symbols, sizeof(char*) * size);
    else symbols = (char**) malloc(sizeof(char*) * size);
  }

  for (i=0; i<index; i++)
    if (!strcmp(name, symbols[i]))
      return symbols[i];

  /* not found, i==index */
  symbols[index++] = strdup(name);
  return symbols[i];
}

#ifdef FLEX_SCANNER
int syst_input()
{
    return( input()) ;
}
#endif

int yywrap(void)
{
#ifdef FLEX_SCANNER
    yy_init = 1 ;
#endif
    return( 1 ) ;
}

void sc_init_lex(void)
{
    /*yyrestart(); */
    BEGIN TEXT;
}

extern bool syst_syntax_error;

int syst_error(char *s)
{
	/* procedure minimun de recouvrement d'erreurs */
/*	int c;*/

	(void) fprintf(stderr,"%s near %s\n",s,yytext);
/*	while ((c = getchar()) != EOF)
		putchar(c);
*/
	syst_syntax_error = true;
	return true;
}



