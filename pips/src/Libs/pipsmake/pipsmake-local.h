/*

  $Id: pipsmake-local.h 23656 2022-05-08 06:45:50Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of PIPS.

  PIPS is free software: you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with PIPS.  If not, see <http://www.gnu.org/licenses/>.

*/
#include "makefile.h"
typedef bool (*pipsmake_callback_handler_type)(void);

/* symbols exported by lex / yacc */
extern void pipsmake_error(const char *);
extern FILE *pipsmake_in;
extern int pipsmake_lex(void);
extern int pipsmake_parse(void);

/* work around cproto 4.7t issue */
/* symbols from readmakefile.y */
extern void yyerror(const char *);
extern void fprint_virtual_resources(FILE *, const char *, list);
extern void fprint_makefile(FILE *, makefile);
extern makefile parse_makefile(void);
extern rule find_rule_by_phase(const char *);
extern void add_rule(rule);
extern makefile open_makefile(const char *);
extern void save_makefile(const char *);
extern bool close_makefile(const char *);
/* symbols form lexer.l */
extern int yywrap(void);
extern int init_lex(void);
extern void yyerror_lex_part(const char *);
