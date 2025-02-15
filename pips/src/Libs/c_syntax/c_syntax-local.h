/*

  $Id: c_syntax-local.h 23657 2022-05-09 10:40:27Z coelho $

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

#include "c_parser_private.h"

extern FILE * c_in; /* the file read in by the c_lexer */
extern int c_lineno ;
extern int c_lex();
extern int c_parse();

/* The labels in C have function scope... but beware of
   inlining... and conflict with user labels */
/* To disambiguate labels, in case inlining is performed later and to
   suppress the potential for conflicts with user labels.

   Temporary entities have to be generated to be replaced later by the
   final labels. The temporary entities should be eliminated from the
   symbol table...
 */
#define get_label_prefix() "-"  // a character that cannot be used in a correct

/* These global variables are declared in ri-util/util.c */
extern entity DynamicArea;
extern entity StaticArea;
extern entity HeapArea;
extern entity StackArea;
extern entity AllocatableArea;

/* Error handling */
#define FIRST_C_LINE_NUMBER (1)
#define UNDEFINED_C_LINE_NUMBER (-1)

#define CParserError(m) c_parser_error(CURRENT_FUNCTION, m)
#define c_parser_user_warning(...)                                      \
  c_parser_user_warning_func(CURRENT_FUNCTION, __FILE__, __LINE__, __VA_ARGS__)

/* cproto workaround */
/* from "cyacc.y" */
extern entity GetFunction(void);
extern void reset_expression_comment(void);
extern string pop_block_scope(string /*old_scope*/);
extern string scope_to_block_scope(string /*full_scope*/);
extern c_parser_context CreateDefaultContext(void);
extern void InitScope(void);
extern int ScopeStackSize(void);
extern string GetScope(void);
extern string GetParentScope(void);
extern void ExitScope(void);
extern void PushContext(c_parser_context /*c*/);
extern void PopContext(void);
extern c_parser_context GetContext(void);
extern c_parser_context GetContextCopy(void);
extern void reset_declaration_counter(void);
extern int get_declaration_counter(void);
extern void init_c_parser_scope_stack(void);
extern void reset_c_parser_scope_stack(void);
extern void force_reset_c_parser_scope_stack(void);
extern void push_new_c_parser_scope(void);
extern void pop_c_parser_scope_stack(void);
extern bool c_parser_scope_stack_empty_p(void);
extern string get_c_parser_current_scope(void);
extern string get_c_parser_nth_scope(int /*n*/);
extern int c_parser_number_of_scopes(void);
/* from "clex.l" */
extern int C_line_increment;
extern int get_previous_c_lineno(void);
extern unsigned int character_occurences_in_string(string /*s*/, char /*c*/);
extern int get_current_C_line_number(void);
extern int get_previous_C_line_number(void);
extern void set_current_C_line_number(void);
extern void push_current_C_line_number(void);
extern int pop_current_C_line_number(void);
extern void reset_current_C_line_number(void);
extern void error_reset_current_C_line_number(void);
extern void reset_token_has_been_seen_p(void);
extern string get_current_C_comment(void);
extern void push_current_C_comment(void);
extern string pop_current_C_comment(void);
extern void update_C_comment(string /*a_comment*/);
extern void remove_LFs_from_C_comment(int /*extra_LF*/);
extern void discard_C_comment(void);
extern void reset_C_comment(bool /*is_compilation_unit_p*/);
extern void error_reset_C_comment(bool /*is_compilation_unit_p*/);
extern void clear_C_comment(void);
extern void init_C_comment(void);
extern void c_error(char * /*msg*/);
extern void c_reset_lex(void);
extern int c_wrap(void);
