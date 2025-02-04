/*
  $Id$

  Copyright 1989-2017 MINES ParisTech

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
  along with PIPS. If not, see <http://www.gnu.org/licenses/>.
*/

#ifdef HAVE_CONFIG_H
#include "pips_config.h"
#endif

#include "genC.h"
#include "linear.h"
#include "misc.h"

#include "ri-util.h"
#include "ri.h"

#include "prettyprint.h"
#include "properties.h"

#include "freia.h"
#include "hwac.h"

#include "freia_mppa.h"

/**
 * @brief Default number of memory slots
 */
#define MPPA_DEFAULT_SMEM_SLOTS 4

/**
 * @brief Placeholder for an undefined slot
 */
#define SMEM_SLOT_UNDEFINED get_int_property("HWAC_MPPA_MAX_SMEM_SLOTS")

/**
 * @brief Array of vertices using SMEM slots (indices) as output
 *
 * Links a SMEM slot to a dagvtx user, or NULL if unused
 */
static dagvtx *smem_slot_users;

/**
 * @brief Get first unused SMEM slot
 */
static _int get_free_slot() {
  unsigned int max_smem_slots = get_int_property("HWAC_MPPA_MAX_SMEM_SLOTS");
  _int slot = SMEM_SLOT_UNDEFINED;
  for (unsigned int i = 0; i < max_smem_slots; i++) {
    if (smem_slot_users[i] == NULL) {
      slot = i;
      break;
    }
  }
  pips_assert("enough SMEM slots", slot != SMEM_SLOT_UNDEFINED);
  return slot;
}

/**
 * @brief Get output slot used by input vertex
 */
static _int get_output_slot(dagvtx vtx) {
  unsigned int max_smem_slots = get_int_property("HWAC_MPPA_MAX_SMEM_SLOTS");
  _int slot = SMEM_SLOT_UNDEFINED;
  for (unsigned int i = 0; i < max_smem_slots; i++) {
    if (smem_slot_users[i] == vtx) {
      slot = i;
      break;
    }
  }
  return slot;
}

/**
 * @brief Provide a valid unused SMEM slot and link it to vertex
 *
 * @param[in] vtx vertex in need of a memory slot
 * @param[out] slot_users_ht number of uses for this slot
 *
 * @return valid SMEM slot
 */
static _int get_a_smem_slot(const dagvtx vtx, hash_table slot_uses_ht) {

  /* get first unused slot */
  _int slot = get_free_slot();
  /* link this slot to current vtx for later use */
  smem_slot_users[slot] = vtx;

  _int nb_succs = gen_length(dagvtx_succs(vtx));
  if (nb_succs > 0) {
    /* several successors, slot should be stored */
    hash_put(slot_uses_ht, vtx, (void *)nb_succs);
    /* and the consumer should deal itself with freeing the slot */
  }

  return slot;
}

/**
 * @brief Try to find a reusable memory slot for in-place operators
 *
 * @param[in] vtx current vertex
 * @param[in] preds list of predecessors of current vertex
 * @param[in,out] slot_uses_ht number of uses for this slot
 *
 * @return one of preds slots, or SMEM_SLOT_UNDEFINED
 */
static _int reuse_pred_slot(const dagvtx vtx, const list preds,
                            hash_table slot_uses_ht) {

  _int slot = SMEM_SLOT_UNDEFINED;
  if (dagvtx_optype(vtx) == spoc_type_poc) {
    return slot;
  }
  FOREACH(dagvtx, pred, preds) {
    _int pred_rem_use = (_int)hash_get(slot_uses_ht, pred);
    if (pred_rem_use == 0) {
      /* pred slot can be reused */
      slot = get_output_slot(pred);
      smem_slot_users[slot] = vtx;
      hash_update(slot_uses_ht, pred, (void *)(pred_rem_use - 1));
      break;
    }
  }
  _int nb_succs = gen_length(dagvtx_succs(vtx));
  if (nb_succs > 0) {
    /* several successors, slot should be stored */
    hash_put(slot_uses_ht, vtx, (void *)nb_succs);
  }
  return slot;
}

/**
 * @brief Provide vertex used SMEM slot, update uses table
 *
 * @param[in] vtx vertex using an output slot
 * @param[out] slot_uses_ht number of uses for this slot
 *
 * @return valid SMEM slot
 */
static _int use_output_slot(const dagvtx vtx, hash_table slot_uses_ht) {
  _int slot = get_output_slot(vtx);
  _int rem_uses = (_int)hash_get(slot_uses_ht, vtx);
  /* update uses */
  hash_update(slot_uses_ht, vtx, (void *)(rem_uses - 1));

  return slot;
}

/**
 * @brief Update preds usage table, unused slot list
 *
 * @param[in] vtx_preds list of predecessors
 * @param[out] slot_users_ht number of uses
 *
 * @return void
 */
static void process_used_slots(list vtx_preds, hash_table slot_uses_ht) {
  FOREACH(dagvtx, pred, vtx_preds) {
    _int slot = get_output_slot(pred);
    _int rem_uses = (_int)hash_get(slot_uses_ht, pred);
    if (rem_uses == 0) {
      /* can reuse slot */
      smem_slot_users[slot] = NULL;
      /* delete entry in uses ht */
      hash_del(slot_uses_ht, pred);
    }
  }
}

/**
 * @brief Replace dots in string with underscores
 *
 * @param[in,out] str allocated string with (or without) dots
 *
 * @return input string
 */
static string dots2us(string str) {
  unsigned long len = strlen(str);
  for (unsigned int i = 0; i < len; i++) {
    if (str[i] == '.') {
      str[i] = '_';
    }
  }
  return str;
}

/**
 * @brief Build a dag list of arguments and a string of corresponding parameters
 *
 * @param[in] cdg current dag
 * @param[out] args allocated empty list of arguments (entities)
 * @param[out] fargs pointer to string of helper parameters
 *
 * @return allocated list of helper call arguments
 */
static list mppa_helper_args_params(const dag cdg, string *params) {

  /* list of argument expressions */
  list largs = NIL;

  /* string buffer of helper parameters */
  string_buffer sb_args = string_buffer_make(true);

  /* loop over input/output nodes and store image variables into list */
  set im_done = set_make(set_string);
  FOREACH(dagvtx, vtx, dag_inputs(cdg)) {
    entity in = dagvtx_image(vtx);
    if (in) {
      expression inexpr = entity_to_expression(in);
      if (!set_belong_p(im_done, expression_to_string(inexpr))) {
        largs = CONS(expression, inexpr, largs);
        set_add_element(im_done, im_done, expression_to_string(inexpr));
      }
    }
  }
  largs = gen_nreverse(largs);
  list largsout = NIL;
  FOREACH(dagvtx, vtx, dag_outputs(cdg)) {
    entity out = dagvtx_image(vtx);
    if (out) {
      expression outexpr = entity_to_expression(out);
      if (!set_belong_p(im_done, expression_to_string(outexpr))) {
        largsout = CONS(expression, outexpr, largsout);
        set_add_element(im_done, im_done, expression_to_string(outexpr));
      }
    }
  }
  set_free(im_done);
  largs = gen_nconc(gen_nreverse(largsout), largs);

  /* loop over image expressions to fill string buffer */
  FOREACH(expression, imexpr, largs) {
    sb_prf(sb_args, "freia_data2d *%s, ", expression_to_string(imexpr));
  }

  /* loop over measure vertices */
  FOREACH(dagvtx, vtx, dag_vertices(cdg)) {
    if (dagvtx_is_measurement_p(vtx)) {
      list measargs = gen_full_copy_list(freia_get_vertex_params(vtx));
      sb_prf(sb_args, "int32_t %s, ",
             expression_to_string(EXPRESSION(CAR(measargs))));
      if (gen_length(measargs) >= 3) {
        string xcoord = expression_to_string(EXPRESSION(gen_nth(1, measargs)));
        string ycoord = expression_to_string(EXPRESSION(gen_nth(2, measargs)));
        sb_prf(sb_args, "uint32_t %s, ", dots2us(xcoord));
        sb_prf(sb_args, "uint32_t %s, ", dots2us(ycoord));
      }
      largs = gen_nconc(largs, measargs);
    }
  }

  set se_done = set_make(set_string);
  FOREACH(dagvtx, vtx, dag_vertices(cdg)) {
    /* non partially evaluated structuring elements */
    if (dagvtx_optype(vtx) == spoc_type_poc) {
      intptr_t se[9];
      if (!freia_extract_kernel_vtx(vtx, true, &se[0], &se[1], &se[2], &se[3],
                                    &se[4], &se[5], &se[6], &se[7], &se[8])) {
        /* pass SE name as helper parameter */
        list params = gen_full_copy_list(freia_get_vertex_params(vtx));
        string se = expression_to_string(EXPRESSION(CAR(params)));
        if (!set_belong_p(se_done, se)) {
          sb_prf(sb_args, "int32_t *%s, ", se);
          largs = gen_nconc(largs, params);
          set_add_element(se_done, se_done, se);
        }
      }
    }
  }
  set_free(se_done);

  /* post-process parameters */
  string fargs = string_buffer_to_string(sb_args);
  /* arguments string ends with ", " */
  if (fargs[strlen(fargs) - 2] == ',') {
    fargs[strlen(fargs) - 2] = '\0';
  }
  /* replace '&' by '*' */
  for (unsigned int i = 0; i < strlen(fargs); i++) {
    if (fargs[i] == '&') {
      fargs[i] = '*';
    }
  }
  *params = fargs;

  /* cleanup */
  string_buffer_free(&sb_args);
  return largs;
}

/**
 * @brief Replace FREIA calls by PIPS generated ones
 *
 * @param[in] dg dag of several FREIA operations
 * @param[in] fname function to call
 * @param[in] split splitted dag index
 *
 * @return void
 */
static void mppa_call_helper(const dag dg, const string fname,
                             unsigned int dagi, list largs) {
  bool call_inserted = false;
  FOREACH(dagvtx, v, dag_vertices(dg)) {
    _int op = dagvtx_opid(v);
    if (op == 0)
      continue;
    statement st = dagvtx_statement(v);
    if (call_inserted)
      hwac_replace_statement(st, freia_ok(), true);
    else {
      entity mppa_helper = local_name_to_top_level_entity(fname);
      string fname_real = strdup(cat(fname, "_", i2a(dagi)));
      if (entity_undefined_p(mppa_helper))
        mppa_helper = freia_create_helper_function(fname_real, NIL);
      hwac_replace_statement(st, make_call(mppa_helper, largs), false);
      call_inserted = true;
    }
  }
}

/**
 * @brief Generate an optimized, FREIA-MPPA low level version of this dag
 *
 * @param[in] module current module name
 * @param[in] cdg current dag
 * @param[in] fname function name
 * @param[in] dagi dag index
 * @param[in,out] helper file to host the output
 *
 * @return void
 */
static void mppa_compile_dag(const string module, const dag cdg,
                             const string fname, const int dagi,
                             FILE *const helper) {

  fprintf(helper, "\n// module=%s fname=%s split=%d\n", module, fname, dagi);

  /* debug */
#ifdef DEBUG_INFO
  dag_dump(stdout, fname, cdg);
#endif /* DEBUG_INFO */

  string_buffer sb_cmd = string_buffer_make(true);
  string curr_cmd = strdup(cat("cmd", i2a(dagi)));
  unsigned int meas_ctr = 0;
  hash_table meas_off_ht = hash_table_make(hash_pointer, 16);
  unsigned int instr_ctr = 0;
  hash_table slots_used_ht = hash_table_make(hash_pointer, 16);
  list ordered_vtx = gen_nreverse(gen_copy_seq(dag_vertices(cdg)));

  unsigned int max_smem_slots = get_int_property("HWAC_MPPA_MAX_SMEM_SLOTS");

  /* slot -> dagvtx user or NULL if free */
  smem_slot_users = malloc(max_smem_slots * sizeof(dagvtx));
  for (unsigned int i = 0; i < max_smem_slots; i++) {
    smem_slot_users[i] = NULL;
  }

  string fparams;
  list largs = mppa_helper_args_params(cdg, &fparams);

  /* prologue */
  sb_prf(sb_cmd, "int %s_%d(%s) {\n", fname, dagi, fparams);
  sb_cat(sb_cmd, "\n");
  sb_cat(sb_cmd, "  mppa_cc_instr_t *instrs;\n"); /* global? */
  sb_cat(sb_cmd, "  unsigned int i = 0;\n");      /* global? */
  sb_prf(sb_cmd, "  mppa_cc_cmd_t %s;\n", curr_cmd);
  sb_prf(sb_cmd, "  instrs = %s.instrs;\n", curr_cmd);
  /* set number of SMEM slots using property set to non-default value */
  if (max_smem_slots != MPPA_DEFAULT_SMEM_SLOTS) {
    pips_assert("non-null number of SMEM slots", max_smem_slots > 0);
    pips_assert("enough number of SMEM slots", max_smem_slots < 255);
    sb_cat(sb_cmd, "  /* override default SMEM slots number */\n");
    sb_prf(sb_cmd, "  mppa_smem_slots = %d;\n", max_smem_slots);
  }
  sb_cat(sb_cmd, "\n");

  FOREACH(dagvtx, vtx, ordered_vtx) {

    const freia_api_t *fapi = get_freia_api_vtx(vtx);
    list preds = dag_vertex_preds(cdg, vtx);

    /* input nodes */
    if (same_string_p(dagvtx_operation(vtx), "undefined")) {
      entity imin = dagvtx_image(vtx);
      sb_cat(sb_cmd, "  instrs[i].kind = MPPA_CMD_GET_IO_TILE;\n");
      sb_prf(sb_cmd,
             "  instrs[i].com.io_pos = ((io_image_h *)%s->mppa_ptr)->pos;\n",
             expression_to_string(entity_to_expression(imin)));
      /* put image in an unused SMEM slot */
      sb_prf(sb_cmd, "  instrs[i].com.cc_pos = %d;\n",
             get_a_smem_slot(vtx, slots_used_ht));
    }

    else { /* non-input nodes */
      sb_prf(sb_cmd, "  instrs[i].kind = MPPA_CMD_EXECUTE_KERNEL;\n");
      sb_prf(sb_cmd, "  instrs[i].opr.kernel = %s;\n", fapi->mppa.kernel_enum);

      /* loop over preds to get slots */
      unsigned int predi = 0;
      FOREACH(dagvtx, pred, preds) {
        sb_prf(sb_cmd, "  instrs[i].opr.pos[%d] = %d; /* input */\n", predi + 1,
               use_output_slot(pred, slots_used_ht));
        predi++;
      }

      if (dagvtx_is_measurement_p(vtx)) { /* reductions results */
        string measvar =
            expression_to_string(EXPRESSION(CAR(freia_get_vertex_params(vtx))));
        /* remove '&' in first position */
        if (measvar[0] == '&') {
          measvar = &measvar[1]; /* good memory management \o/ */
        }
        sb_prf(sb_cmd, "  instrs[i].opr.red_dst[0] = %s; /* result */\n",
               measvar);
        if (fapi->arg_misc_out > 1) {
          /* store vtx -> offset variable id */
          hash_put(meas_off_ht, vtx, (void *)(_int)meas_ctr);
          /* declare offset variable */
          sb_prf(sb_cmd, "  uint32_t meas_off%d;\n", meas_ctr);
          sb_prf(sb_cmd,
                 "  instrs[i].opr.red_dst[1] = &meas_off%d; /* offset */\n",
                 meas_ctr);
          meas_ctr++;
        }
      }

      else { /* there is an output image */

        _int slot = reuse_pred_slot(vtx, preds, slots_used_ht);
        if (slot == SMEM_SLOT_UNDEFINED) {
          /* preds outputs are reused after */
          slot = get_a_smem_slot(vtx, slots_used_ht);
        }

        sb_prf(sb_cmd, "  instrs[i].opr.pos[0] = %d; /* output */\n", slot);

        /* and maybe some extra input parameters... */

        if (dagvtx_optype(vtx) == spoc_type_poc) {
          /* deal with structuring elements */
          intptr_t se[9];
          if (freia_extract_kernel_vtx(vtx, true, &se[0], &se[1], &se[2],
                                       &se[3], &se[4], &se[5], &se[6], &se[7],
                                       &se[8])) {
            /* se is statically known, do some partial eval */
            sb_prf(
                sb_cmd, "  instrs[i].opr.scalars[0] = 0b%d%d%d%d%d%d%d%d%d;\n",
                se[0], se[1], se[2], se[3], se[4], se[5], se[6], se[7], se[8]);
          } else {
            /* use a function to convert se to binary constant */
            sb_prf(sb_cmd, "  instrs[i].opr.scalars[0] = se2scal(%s);\n",
                   expression_to_string(
                       EXPRESSION(CAR(freia_get_vertex_params(vtx)))));
          }
        }

        else {
          /* deal with every parameter of other-than-morphological ops */
          unsigned int argi = 0;
          FOREACH(expression, expr, freia_get_vertex_params(vtx)) {
            /* partial eval threshold third parameter to redirect to
               relevant MPPA kernel */
            if (argi == 2 && dagvtx_optype(vtx) == spoc_type_thr) {
              if (strcmp(expression_to_string(expr), "1") == 0 ||
                  strcmp(expression_to_string(expr), "true") == 0) {
                /* hack: overwrite current kernel... */
                sb_cat(sb_cmd,
                       "  instrs[i].opr.kernel = MPPA_KERNEL_THRESHOLD_BIN;\n");
              }
              /* skip writing third parameter (avoid obvious overflow) */
              break;
            }
            sb_prf(sb_cmd, "  instrs[i].opr.scalars[%d] = %s;\n", argi,
                   expression_to_string(expr));
            argi++;
          }
        }
      }
    }

    /* add put instructions for output nodes (releases slot) */
    if (gen_in_list_p(vtx, dag_outputs(cdg))) {
      sb_prf(sb_cmd, "  i++; /* instr #%u, vtx #%d */\n", instr_ctr,
             dagvtx_number(vtx));
      sb_cat(sb_cmd, "\n");
      instr_ctr++;

      entity imout = dagvtx_image(vtx);
      sb_cat(sb_cmd, "  instrs[i].kind = MPPA_CMD_PUT_IO_TILE;\n");
      sb_prf(sb_cmd, "  instrs[i].com.cc_pos = %d;\n", get_output_slot(vtx));
      sb_prf(sb_cmd,
             "  instrs[i].com.io_pos = ((io_image_h *)%s->mppa_ptr)->pos;\n",
             expression_to_string(entity_to_expression(imout)));
    }

    process_used_slots(preds, slots_used_ht);

    sb_prf(sb_cmd, "  i++; /* instr #%u, vtx #%d */\n", instr_ctr,
           dagvtx_number(vtx));
    sb_cat(sb_cmd, "\n");

    instr_ctr++;
    gen_free_list(preds);
  }

  unsigned int max_instrs_per_cmd =
      get_int_property("HWAC_MPPA_MAX_INSTRS_CMD");
  pips_assert("cmd can host more instructions",
              instr_ctr <= max_instrs_per_cmd);

  /* effectively launch computation */
  sb_cat(sb_cmd, "  /* launch computation... */\n");
  sb_prf(sb_cmd, "  mppa_compute(i, &%s);\n", curr_cmd);
  sb_cat(sb_cmd, "\n");

  /* post-process reductions offset */
  HASH_FOREACH(dagvtx, vtx, _int, value, meas_off_ht) {
    list vtx_params = freia_get_vertex_params(vtx);
    string xcoord = expression_to_string(EXPRESSION(gen_nth(1, vtx_params)));
    string ycoord = expression_to_string(EXPRESSION(gen_nth(2, vtx_params)));
    pips_assert("coord var name contains more than '&' char",
                strlen(xcoord) > 1);
    pips_assert("coord var name contains more than '&' char",
                strlen(ycoord) > 1);
    xcoord = dots2us(&xcoord[1]);
    ycoord = dots2us(&ycoord[1]);
    string imin = expression_to_string(entity_to_expression(
        ENTITY(CAR(vtxcontent_inputs(dagvtx_content(vtx))))));
    sb_prf(sb_cmd, "  *%s = meas_off%d %% %s->widthWa;\n", xcoord, value, imin);
    sb_prf(sb_cmd, "  *%s = meas_off%d / %s->widthWa;\n", ycoord, value, imin);
    sb_cat(sb_cmd, "\n");
  }

  /* epilogue */
  sb_cat(sb_cmd, "  return 0;\n");
  sb_cat(sb_cmd, "}\n");

  /* dump to helper file */
  string_buffer_to_file(sb_cmd, helper);

  /* replace statements */
  mppa_call_helper(cdg, fname, dagi, largs);

  /* cleanup */
  string_buffer_free(&sb_cmd);
  hash_table_free(meas_off_ht);
  hash_table_free(slots_used_ht);
  free(smem_slot_users);
  gen_free_list(ordered_vtx);
}

/**
 * @brief Split a dag into several subdags
 *
 * @param[in] dg input dag
 * @param[in] n_dags number of returned sub-dags
 * @param[in] n_vtx_dag number of vertices per sub-dag
 *
 * @return list of sub-dags
 */
static list mppa_dag_split(const dag dg, unsigned int n_dags,
                           unsigned int n_vtx_dag) {
  list res = NIL;
  unsigned int upper_bound = get_int_property("HWAC_MPPA_MAX_INSTRS_CMD");

  for (unsigned int i = 0; i < n_dags; i++) {

    list vertices = NIL, inputs = NIL, outputs = NIL;

    unsigned int vtxi = 0;
    FOREACH(dagvtx, vtx, dag_vertices(dg)) {
      if (vtxi >= i * n_vtx_dag && vtxi < (i + 1) * n_vtx_dag) {
        vertices = CONS(dagvtx, vtx, vertices);
        if (gen_in_list_p(vtx, dag_inputs(dg))) {
          inputs = CONS(dagvtx, vtx, inputs);
        }
        if (gen_in_list_p(vtx, dag_outputs(dg))) {
          outputs = CONS(dagvtx, vtx, outputs);
        }
      }
      vtxi++;
    }

    /* add input nodes */
    list to_add = NIL;
    FOREACH(dagvtx, vtx, vertices) {
      FOREACH(dagvtx, pred, dag_vertex_preds(dg, vtx)) {
        if (!gen_in_list_p(pred, vertices)) {
          /* replace by an input node */
          FOREACH(entity, e, vtxcontent_inputs(dagvtx_content(vtx))) {
            /* get the right entity */
            if (e == vtxcontent_out(dagvtx_content(pred))) {
              pips_assert("e is defined", e != entity_undefined);
              /* create an input node of opid 0 (undefined) */
              dagvtx newpred = make_dagvtx(
                  make_vtxcontent(0, 0, make_pstatement_empty(), NIL, e), NIL);

              inputs = CONS(dagvtx, newpred, inputs);
              to_add = CONS(dagvtx, newpred, to_add);

              dagvtx_succs(newpred) = CONS(dagvtx, vtx, dagvtx_succs(newpred));
            }
          }
        }
      }
    }
    /* add input vertex right before first consumer to optimize memory
       slots usage */
    FOREACH(dagvtx, vtx, to_add) {
      dagvtx first_consumer = DAGVTX(CAR(dagvtx_succs(vtx)));
      vertices = gen_insert_before(vtx, first_consumer, vertices);
    }

    /* add output nodes */
    FOREACH(dagvtx, vtx, vertices) {
      FOREACH(dagvtx, succ, dagvtx_succs(vtx)) {
        if (!gen_in_list_p(succ, vertices)) {
          /* mark vtx as an output node */
          outputs = CONS(dagvtx, vtx, outputs);
          /* remove succ from successors list */
          gen_remove(&dagvtx_succs(vtx), succ);
        }
      }
    }

    /* clean some weird cases when an input vtx is also an output*/
    FOREACH(dagvtx, vtx, inputs) {
      if (gen_in_list_p(vtx, outputs)) {
        gen_remove(&outputs, vtx);
      }
    }

    dag subdg = make_dag(gen_nreverse(inputs), gen_nreverse(outputs),
                         gen_nreverse(vertices));

    dag_cleanup_other_statements(subdg);

    pips_assert("small subdags",
                (gen_length(dag_vertices(subdg)) +
                 gen_length(dag_outputs(subdg))) <= upper_bound);

    res = CONS(dag, subdg, res);
  }
  return res;
}

/**
 * @brief Split a dag in several sub-dags if too large
 *
 * @param[in] dag to split
 *
 * @return list of sub-dags of input dag
 */
static list mppa_dag_maybe_split_instrs_cmd(const dag dg) {

  list res = NIL;
  unsigned int upper_bound = get_int_property("HWAC_MPPA_MAX_INSTRS_CMD");
  unsigned int n_instrs =
      gen_length(dag_vertices(dg)) + gen_length(dag_outputs(dg));

  if (n_instrs <= upper_bound) {
    /* ok: dag should not be splitted */
    res = CONS(dag, dg, res);
  } else {
    /* not ok: split! */
    unsigned int n_dags = n_instrs / upper_bound + 1;
    unsigned int n_vtx_dag = n_instrs / n_dags + 1;

    /* one more if maybe too large */
    if (n_vtx_dag > upper_bound - 4) { /* educated guess... */
      n_dags++;
      n_vtx_dag = n_instrs / n_dags + 1;
    }

    pips_assert("splitted dags are small enough", n_vtx_dag <= upper_bound);

    /* constraints: balanced dags, try not to separate outputs from
       producers...  */
    res = mppa_dag_split(dg, n_dags, n_vtx_dag);
  }
  return res;
}

/**
 * @brief Compile one dag with AIPO optimizations
 *
 * @param ls statements underlying the full dag
 * @param occs image occurences
 * @param exchanges statements to exchange because of dependences
 *
 * @return the list of allocated intermediate images
 */
list freia_mppa_compile_calls(string module, dag fulld, sequence sq, list ls,
                              const hash_table occs, hash_table exchanges,
                              const set output_images, FILE *helper_file,
                              __attribute__((__unused__)) set helpers,
                              int number) {

  pips_debug(3, "considering %d statements\n", (int)gen_length(ls));
  pips_assert("some statements", ls);

  // intermediate images
  hash_table init = hash_table_make(hash_pointer, 0);
  list new_images = dag_fix_image_reuse(fulld, init, occs);

  // about aipo statistics: no helper file to put them...
  list added_before = NIL, added_after = NIL;
  freia_dag_optimize(fulld, exchanges, &added_before, &added_after);

  // dump final optimised dag
  dag_dot_dump_prefix(module, "dag_cleaned_", number, fulld, added_before,
                      added_after);

  string fname_fulldag = strdup(cat(module, "_mppa", HELPER, i2a(number)));

  /* split on scalars */
  list ldss = dag_split_on_scalars(
      fulld, NULL, NULL, (gen_cmp_func_t)dagvtx_ordering, NULL, output_images);

  pips_debug(3, "dag initial split in %d dags\n", (int)gen_length(ldss));

  int dagi = 0;

  set stats = set_make(set_pointer), dones = set_make(set_pointer);

  FOREACH(dag, dg, ldss) {

    if (dag_no_image_operation(dg)) {
      continue;
    }

    // fix statements connexity
    dag_statements(stats, dg);
    freia_migrate_statements(sq, stats, dones);
    set_union(dones, dones, stats);

    /* split large dags */
    list sub_dags = mppa_dag_maybe_split_instrs_cmd(dg);

    FOREACH(dag, subdg, sub_dags) {
      mppa_compile_dag(module, subdg, fname_fulldag, dagi, helper_file);
      dagi++;
    }
  }

  set_free(stats);
  set_free(dones);

  // now may put actual allocations, which messes up statement numbers
  list reals =
      freia_allocate_new_images_if_needed(ls, new_images, occs, init, NULL);

  // ??? should it be NIL because it is not useful in AIPO->AIPO?
  freia_insert_added_stats(ls, added_before, true);
  added_before = NIL;
  freia_insert_added_stats(ls, added_after, false);
  added_after = NIL;

  // cleanup
  gen_free_list(new_images);
  hash_table_free(init);

  return reals;
}
