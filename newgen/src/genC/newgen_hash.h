/*

  $Id: newgen_hash.h 1357 2016-03-02 08:18:50Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of NewGen.

  NewGen is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or any later version.

  NewGen is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
  License for more details.

  You should have received a copy of the GNU General Public License along with
  NewGen.  If not, see <http://www.gnu.org/licenses/>.

*/

#ifndef newgen_hash_included
#define newgen_hash_included

#define HASH_DEFAULT_SIZE 7

/* Equality and rank functions are provided for strings, integers,
   pointers and Newgen chunks. The user can provide his/her own
   functions by using hash_private. */
typedef enum hash_key_type {
  hash_string, hash_int, hash_pointer, hash_chunk, hash_private
} hash_key_type;

/* Define hash_table structure which is hidden.
 * The only thing we know about it is that the entries are in an array
 * pointed to by hash_table_array(htp), it contains hash_table_size(htp)
 * elements. These elements can be read with hash_entry_val(...) or
 * hash_entry_key(...). If the key is HASH_ENTRY_FREE or
 * HASH_ENTRY_FREE_FOR_PUT then the slot is empty.
 */

typedef struct __hash_table *hash_table;
typedef _uint (* hash_rank_t)(const void *, size_t);
typedef int (* hash_equals_t)(const void *, const void *);

/* Value of an undefined hash_table
 */
#define hash_table_undefined ((hash_table)gen_chunk_undefined)
#define hash_table_undefined_p(h) ((h)==hash_table_undefined)

/* value returned by hash_get() when the key is not found; could also be
   called HASH_KEY_NOT_FOUND, but it's semantically a value; this bottom
   value will be user-definable in a future release of NewGen */

#define HASH_UNDEFINED_VALUE ((void *) gen_chunk_undefined)

#define hash_table_empty_p(htp) (hash_table_entry_count(htp) == 0)

#define HASH_MAP(k, v, code, ht)                                  \
  {                                                               \
    hash_table NGMID(h) = (ht) ;                                  \
    register void * NGMID(i) = NULL;                              \
    void *k, *v;                                                  \
    while ((NGMID(i) =                                            \
            hash_table_scan(NGMID(h), NGMID(i), &k, &v))) {       \
      code;                                                       \
    }                                                             \
  }

#define HASH_FOREACH(key_type, k, value_type, v, ht)                    \
  hash_table NGMID(h) = (ht);                                           \
  register void * NGMID(i) = NULL;                                      \
  key_type k;                                                           \
  value_type v;                                                         \
  while((NGMID(i) =                                                     \
         hash_table_scan(NGMID(h), NGMID(i), (void**) &k, (void**) &v)))

// hash_put_or_update() uses the warn_on_redefinition
#define hash_put_or_update(h, k, v) hash_overwrite(h, k, v)

// functions implemented in hash.c

// MISC
extern void hash_warn_on_redefinition(void);
extern void hash_dont_warn_on_redefinition(void);
extern bool hash_warn_on_redefinition_p(void);

// CONSTRUCTORS
extern hash_table hash_table_generic_make(hash_key_type key_type,
					  size_t size,
					  hash_equals_t equals_p,
					  hash_rank_t rank);
extern hash_table hash_table_make(hash_key_type key_type, size_t size);

// DESTRUCTOR
extern void hash_table_free(hash_table);

// OPERATIONS
extern void hash_table_clear(hash_table);
extern void * hash_delget(hash_table, const void *, void **);
extern void * hash_del(hash_table, const void *);
extern void * hash_get(const hash_table, const void *);
extern list hash_get_default_empty_list(const hash_table, const void *);

extern void hash_put(hash_table, const void *, const void *);
extern void hash_update(hash_table, const void *, const void *);
extern bool hash_defined_p(const hash_table, const void *);
extern void hash_overwrite(hash_table, const void *, const void *);

// DUMP
extern void hash_table_print_header(const hash_table, FILE *);
extern void hash_table_print(const hash_table);
extern void hash_table_fprintf(FILE *, gen_string_func_t, gen_string_func_t,
			       const hash_table);

// OBSERVERS
extern int hash_table_entry_count(const hash_table);
extern int hash_table_size(const hash_table);
extern int hash_table_own_allocated_memory(const hash_table);
extern hash_key_type hash_table_type(const hash_table);
extern hash_equals_t hash_table_equals_function(const hash_table);
extern hash_rank_t hash_table_rank_function(const hash_table);
extern void * hash_table_scan(const hash_table, void *, void **, void **);

// MAP STUFF (for newgen generated code based on hash tables)
extern void * hash_map_get(const hash_table, const void *);
extern void hash_map_put(hash_table, const void *, const void *);
extern void hash_map_update(hash_table, const void *, const void *);
extern void * hash_map_del(const hash_table, const void *);
extern bool hash_map_defined_p(const hash_table, const void *);

// UTILS
extern _uint hash_string_rank(const void *, size_t);

#endif // newgen_hash_included

/*  that is all
 */
