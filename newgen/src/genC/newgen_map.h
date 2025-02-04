/*

  $Id: newgen_map.h 1357 2016-03-02 08:18:50Z coelho $

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

#ifndef newgen_map_included
#define newgen_map_included

/*
 * These are the functions defined in the Newgen map library.
 */

#define HASH_GET(start,image,h,k)                         \
  hash_map_get((const hash_table)(h), (const void *)(k))
#define HASH_BOUND_P(start, image, h, k)                        \
  hash_map_defined_p((const hash_table)(h), (const void *)(k))
#define HASH_UPDATE(start,image,h,k,v)                        \
  hash_map_update((h), (const void *)(k), (const void *)(v))
#define HASH_EXTEND(start,image,h,k,v)                    \
  hash_map_put((h), (const void *)(k), (const void *)(v))
#define HASH_DELETE(start,image,h,k)            \
  hash_map_del((h), (const void *)(k))

// rather use FOREACH version below?
#define FUNCTION_MAP(type, start, image, k, v, code, fun)               \
  {                                                                     \
    type NGMID(f) = (fun);                                              \
    hash_table NGMID(h) = (type##_hash_table(NGMID(f)));                \
    register void * NGMID(i) = NULL;                                    \
    gen_chunk * NGMID(k);                                               \
    gen_chunk * NGMID(v);                                               \
    while ((NGMID(i) =                                                  \
            hash_table_scan(NGMID(h), NGMID(i),                         \
                            (void**) &NGMID(k), (void**) &NGMID(v))))   \
    {                                                                   \
      type##_key_type k = (type##_key_type) (NGMID(k))->start ;         \
      type##_value_type v = (type##_value_type) (NGMID(v))->image;      \
      code ;                                                            \
    }                                                                   \
  }

// see also HASH_FOREACH
#define FUNCTION_FOREACH(type, key, val, k, v, fun)                     \
  type NGMID(f) = fun;                                                  \
  message_assert("check domain",                                        \
                 NGMID(f) && type##_defined_p(NGMID(f)) &&              \
                 type##_domain_number(NGMID(f)) == type##_domain);      \
  hash_table NGMID(h) = type##_hash_table(NGMID(f));                    \
  type##_key_type k;                                                    \
  type##_value_type v;                                                  \
  gen_chunk * NGMID(k);                                                 \
  gen_chunk * NGMID(v);                                                 \
  for (register void * NGMID(i) = NULL;                                 \
       ((NGMID(i) =                                                     \
         hash_table_scan(NGMID(h), NGMID(i),                            \
                         (void**) & NGMID(k), (void**) & NGMID(v))),    \
        k = (type##_key_type) (NGMID(i)? NGMID(k)->key: NULL),          \
        v = (type##_value_type) (NGMID(i)? NGMID(v)->val: NULL),        \
        NGMID(i));)

#endif /* newgen_map_included */
