/*

  $Id: freia_sigmac.c 23443 2017-10-27 14:14:05Z guillou $

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

#ifdef HAVE_CONFIG_H
#include "pips_config.h"
#endif

#include <stdint.h>
#include <stdlib.h>
#include <ctype.h>

#include "genC.h"
#include "misc.h"
#include "linear.h"

#include "ri.h"
#include "ri-util.h"
#include "prettyprint.h"
#include "properties.h"

#include "freia.h"
#include "hwac.h"

#include "freia_sigmac.h"

/*#######################################################################*/
/*#######################################################################*/
/*#######################################################################*/

#define SIGMAC_INSTANTIATE(a, b) "    agent " a " = new " b ";\n"
#define SIGMAC_CONNECT(a, b) "    connect (" a ", " b ");\n"
#define REPLICATION_AGENT "rep" //"Dup<int16_t>"

// global variable to store the total number of dags processed
static int n_dags = 0;

/* Populates the hash table htid:
 * one dagvtx is linked to an unique id depending on its freia_api_t
 */
static void sigmac_name_instances(dag dg, hash_table htid) {
  _int nb_op;
  const freia_api_t *f;

  // freia_api_t * -> number of encoutered vertices
  hash_table htinst = hash_table_make(hash_pointer, 16);

  FOREACH(dagvtx, vtx, dag_vertices(dg)) {
    f = get_freia_api_vtx(vtx);
    if (!f)
      continue;

    // initializating hash_table htinst
    if (!hash_defined_p(htinst, f))
      hash_put(htinst, f, (void *)(_int)0);

    // new instance id = total nb of instances of the same operation
    nb_op = (_int)hash_get(htinst, f);
    hash_put(htid, vtx, (void *)nb_op);
    // updating nb of instances for current operation
    nb_op++;
    hash_update(htinst, f, (void *)nb_op);
  }

  hash_table_free(htinst);
}

/* Generate a unique string per dagvtx consisting in
 * - one short name, shared by all the dagvtx with the same freia_api_t
 * - one integer, different for every dagvtx with the same freia_api_t
 */
static string sc_vtx_tostring(const dagvtx v, const hash_table htid) {
  string r = get_freia_api_vtx(v)->sigmac.inst_prefix;
  _int n = (_int)hash_get(htid, v);
  return strdup(cat(r, i2a(n)));
}

/* Determine if an argument contains references to other variables
 * (dirty hack based on isalpha)
 */
static bool is_param_dynamic(expression arg) {
  string s = expression_to_string(arg);
  bool is_dyn = false;
  unsigned int i;
  for (i = 0; i < strlen(s); i++)
    if (isalpha(s[i]))
      is_dyn = true;
  return is_dyn;
}

/* Determine if a dagvtx has at least one dynamic parameter
 */
static bool has_vtx_dynamic_params(dagvtx v) {
  const freia_api_t *f = get_freia_api_vtx(v);
  if (!f)
    return false;
  if (strstr(f->function_name, "_const") || dagvtx_optype(v) == spoc_type_thr) {
    list vtx_params = freia_get_vertex_params(v);
    FOREACH(expression, arg, vtx_params) {
      if (is_param_dynamic(arg))
        return true;
    }
  }
  return false;
}

/* Returns a list of values
   of one dagvtx misc input parameters
 */
static list sc_get_params_values(dagvtx vtx, hash_table hparams, int *nparams) {
  vtxcontent vtc = dagvtx_content(vtx);
  statement stm = pstatement_statement(vtxcontent_source(vtc));
  call c = freia_statement_to_call(stm);

  // list of misc param values
  return freia_extract_params(dagvtx_opid(vtx), call_arguments(c), NULL, NULL,
                              hparams, nparams);
}

/* Print the value of a morphological kernel
 * extracted from a dagvtx
 */
static bool sc_print_kernel(string_buffer sb_par, dagvtx v) {
  intptr_t k[9];
  bool b = freia_extract_kernel_vtx(v, true, &k[0], &k[1], &k[2], &k[3], &k[4],
                                    &k[5], &k[6], &k[7], &k[8]);
  sb_cat(sb_par, "{ ");
  for (int i = 0; i < 8; i++)
    sb_prf(sb_par, "%d, ", k[i]);
  sb_prf(sb_par, "%d }", k[8]);
  return b;
}

/* Print a kernel customized inner loop from
   a morphological kernel
*/
static bool sc_kernel_compute_loop(string_buffer sb_morpho, const dagvtx vtx,
                                   string kname) {
  intptr_t k[9];

  if (dagvtx_optype(vtx) != spoc_type_poc)
    return false;

  bool b = freia_extract_kernel_vtx(vtx, true, &k[0], &k[1], &k[2], &k[3],
                                    &k[4], &k[5], &k[6], &k[7], &k[8]);

  string row[3] = {"olid", "clid", "ilid"};
  int i, j;

  sb_prf(sb_morpho, "\n"
                    "#define %s_%d(OPR)\t\t\t\t\\\n",
         kname, n_dags);
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++)
      if (k[3 * i + j]) {
        string neighbor = strdup(cat("buffer[", row[i], "][i+", i2a(j), "]"));
        sb_prf(sb_morpho, "ret = PIXEL_ ## OPR(ret, %s);\t\\\n", neighbor,
               neighbor);
      }
  sb_prf(sb_morpho, "\nCUSTOM_MORPHO_AGENT(%s_%d, " PIXEL_T ")\n"
                    "\n",
         kname, n_dags);

  return b;
}

static void sc_kernel_specific_agent(string_buffer sb_morpho,
                                     hash_table hparams, const dag dg) {
  list lparams = NIL;

  FOREACH(dagvtx, vtx, dag_vertices(dg)) {

    if (dagvtx_optype(vtx) != spoc_type_poc)
      continue;

    list vtx_param_vars = freia_get_vertex_params(vtx);

    // tests if argument already declared
    string parname =
        (string)hash_get(hparams, EXPRESSION(gen_nth(0, vtx_param_vars)));
    if (gen_in_list_p(parname, lparams))
      continue;
    lparams = CONS(string, parname, lparams);

    sc_kernel_compute_loop(sb_morpho, vtx, parname);
  }
}

/* Generates the constant parameters declaration
 */
static void sigmac_params_decl(string_buffer sb_par, dag dg, hash_table hparams,
                               int *pnparams) {
  // dirty workaround preventing deblocking convolutions
  // to declare several times the same parameter
  list lparams = NIL;
  FOREACH(dagvtx, vtx, dag_vertices(dg)) {

    if (gen_in_list_p(vtx, dag_inputs(dg)) || dagvtx_is_measurement_p(vtx))
      continue;

    // list of misc param values
    list vtx_param_vals = sc_get_params_values(vtx, hparams, pnparams);
    // list of freia misc param names
    list vtx_param_vars = freia_get_vertex_params(vtx);

#ifdef DEBUG_INFO
    const freia_api_t *f = get_freia_api_vtx(vtx);
    sb_prf(sb_par, "// nb args for type %s : %d/%d, in %d, out %d\n",
           f->sigmac.agent_name, gen_length(vtx_param_vals),
           gen_length(vtx_param_vars), f->arg_misc_in, f->arg_misc_out);
    FOREACH(expression, arg, vtx_param_vars) {
      sb_prf(sb_par, "// %s\n", expression_to_string(arg));
    }
    FOREACH(expression, arg, vtx_param_vals) {
      sb_prf(sb_par, "// %s\n", expression_to_string(arg));
    }
#endif

    bool dynamic_agent = has_vtx_dynamic_params(vtx);

    // misc params declaration
    unsigned int i = 0;
    FOREACH(expression, arg, vtx_param_vals) {

      // tests if argument already declared
      string parname =
          (string)hash_get(hparams, EXPRESSION(gen_nth(i, vtx_param_vars)));
      if (gen_in_list_p(parname, lparams))
        continue;
      lparams = CONS(string, parname, lparams);

      if (!dynamic_agent) {
        // print parameter type (in SigmaC, everything is int16_t)
        sb_cat(sb_par, "    " PIXEL_T);

        // print parameter pips name
        sb_prf(sb_par, " %s",
               hash_get(hparams, EXPRESSION(gen_nth(i, vtx_param_vars))));

        // print parameter value
        if (dagvtx_optype(vtx) == spoc_type_poc) {
          // kernel vtx have only one misc parameter
          sb_cat(sb_par, "[9]", " = ");
          sc_print_kernel(sb_par, vtx); // get & print kernel
        } else
          sb_prf(sb_par, " = %s", expression_to_string(arg));

        sb_cat(sb_par, ";\n");

        if (freia_convolution_p(vtx))
          break;
        i++;
      }
    } // FOREACH(expression, arg, vtx_param_vals)
  }
}

/* Generate the instanciation of an agent
 * in the forme "agent instname = new agentname (parameters)"
 */
static void sc_inst(string_buffer sb, const dagvtx v, const hash_table htid,
                    const hash_table hparams, string miscparams,
                    bool is_dynamic) {
  const freia_api_t *f = get_freia_api_vtx(v);
  string_buffer sbinst = string_buffer_make(true);

  // beginning of declaration
  sb_cat(sbinst, f->sigmac.agent_name);

  if (is_dynamic)
    sb_cat(sbinst, "_dyn");

  sb_prf(sbinst, "(%s", f->sigmac.agent_arg);

  // completing with misc arguments
  if ((f->arg_misc_in + f->arg_misc_out) && hparams) {
    if (is_dynamic)
      sb_cat(sbinst, ", height");
    else {
      list largs = freia_get_vertex_params(v);
      FOREACH(expression, arg, largs) {
        sb_cat(sbinst, ", ", hash_get(hparams, arg));
        if (freia_convolution_p(v))
          break;
      }
    }
    // add manually more arguments
    if (miscparams)
      sb_cat(sbinst, ", ", miscparams);
  }
  sb_cat(sbinst, ")");

  if (get_bool_property("HWAC_SIGMAC_SPECIFIC_MORPHO") &&
      dagvtx_optype(v) == spoc_type_poc) {

    string_buffer_reset(sbinst);
    if (same_string_p(f->compact_name, "E8"))
      sb_cat(sbinst, "erode_");
    else if (same_string_p(f->compact_name, "D8"))
      sb_cat(sbinst, "dilate_");
    else if (same_string_p(f->compact_name, "conv"))
      sb_cat(sbinst, "convole_");
    list largs = freia_get_vertex_params(v);
    FOREACH(expression, arg, largs) {
      sb_prf(sbinst, "%s_%d(width, height", hash_get(hparams, arg), n_dags);
      if (freia_convolution_p(v)) // convolution needs the kernel
        sb_prf(sbinst, ", %s", hash_get(hparams, arg));
      sb_prf(sbinst, ")");
      break; // there is only 1 argument
    }
  }

  sb_prf(sb, SIGMAC_INSTANTIATE("%s", "%s"), sc_vtx_tostring(v, htid),
         string_buffer_to_string(sbinst));

  string_buffer_free(&sbinst);
}

/* Helper function
 * determine the input port of the succ dagvtx
 * to be connected to the output port of current_vtx dagvtx
 * succ must be in dagvtx_succs(current_vtx)
 */
static int sc_get_port_id(dagvtx current_vtx, dagvtx succ, dag dg) {
  return gen_position(current_vtx, dag_vertex_preds(dg, succ)) - 1;
}

/* Generate a 3 lines commented code delimiter
 * with a centered title
 */
static void sc_delimiter(string_buffer sb, const string title) {
  sb_cat(sb, "\n\n");
  int columns = 69;
  int i, l = strlen(title);

  // 1st line
  sb_cat(sb, "/*");
  for (i = 0; i < columns; i++)
    sb_cat(sb, "#");
  sb_cat(sb, "*/\n");

  // 2nd line, with title
  sb_cat(sb, "/*");
  int a = (columns - l - 2) / 2;
  for (i = 0; i < a; i++)
    sb_cat(sb, "#");
  if (!(l % 2))
    sb_cat(sb, " ", title, " #");
  else
    sb_cat(sb, " ", title, " ");
  for (i = 0; i < a; i++)
    sb_cat(sb, "#");
  sb_cat(sb, "*/\n");

  // 3rd line, same as 1st one
  sb_cat(sb, "/*");
  for (i = 0; i < columns; i++)
    sb_cat(sb, "#");
  sb_cat(sb, "*/\n");

  sb_cat(sb, "\n");
}

/* Generate an application subgraph header
 * containing the declarations and connections
 * of the i/o agents
 */
static void sc_subgraph_app(string_buffer sb, string subgraph_name,
                            int n_imgs_input, int n_imgs_output,
                            int n_params_input, int n_params_output) {
  sb_prf(sb, "subgraph\n%s\n", subgraph_name);
  sb_cat(sb, "(char pipein[255],\n char pipeout[255],\n",
         " int width,\n int height,\n size_t sizeMax,\n"
         " char pipeparin[255],\n char pipeparout[255])\n"
         "{\n\n");

  sb_cat(sb, "  map {\n");

  // launchers and streamers
  if (n_imgs_input > 0) {
    sb_prf(sb,
           SIGMAC_INSTANTIATE("lhin", "Launcher_In(pipein, %d, width, height)"),
           n_imgs_input);
    sb_prf(sb, SIGMAC_INSTANTIATE("strin", "Streamer_In(width, height, %d)"),
           n_imgs_input);
    sb_cat(sb, SIGMAC_CONNECT("lhin.param", "strin.input"));
    sb_cat(sb, "    SigmaC_agent_setUnitType(strin,\"k1-I/O\");\n");
  }

  if (n_imgs_output > 0) {
    sb_prf(sb, SIGMAC_INSTANTIATE("lhout",
                                  "Launcher_Out(pipeout, %d, width, height)"),
           n_imgs_output);
    sb_prf(sb, SIGMAC_INSTANTIATE("strout", "Streamer_Out(width, height, %d)"),
           n_imgs_output);
    sb_cat(sb, SIGMAC_CONNECT("strout.output", "lhout.result"));
    sb_cat(sb, "    SigmaC_agent_setUnitType(strout,\"k1-I/O\");\n");
  }

  // scalar passing agents
  if (n_params_input > 0) { // transfers dynamic parameters to MPPA
    sb_cat(sb, "\n");
    sb_prf(sb, SIGMAC_INSTANTIATE("pp", "Params_Provider(pipeparin, %d)"),
           n_params_input);
    sb_prf(sb, SIGMAC_INSTANTIATE("sp", "Split<" PARAM_T ">(%d, 1)"),
           n_params_input);
    sb_prf(sb, "    SigmaC_agent_setUnitType(sp,\"k1-I/O\");\n");
    sb_cat(sb, SIGMAC_CONNECT("pp.output", "sp.input"));
  }

  if (n_params_output > 0) { // transfers reduction results to host
    sb_cat(sb, "\n");
    sb_prf(sb, SIGMAC_INSTANTIATE("mr", "Measures_Retriever(pipeparout, %d)"),
           n_params_output);
    sb_prf(sb, SIGMAC_INSTANTIATE("jo", "Join<" PARAM_T ">(%d, 1)"),
           n_params_output);
    sb_prf(sb, "    SigmaC_agent_setUnitType(jo,\"k1-I/O\");\n");
    sb_cat(sb, SIGMAC_CONNECT("jo.output", "mr.input"));
  }
}

/*#######################################################################*/
/*#######################################################################*/
/*#######################################################################*/

static int dagvtx_sigmac_priority(const dagvtx *pv1, const dagvtx *pv2) {
  const dagvtx v1 = *pv1, v2 = *pv2;
  return dagvtx_number(v1) - dagvtx_number(v2);
}

/* If vtx is compound, returns the id of
   correspondant connected component.
   Else returns -1.
 */
static int is_vtx_compound(dagvtx vtx, list lcomponents) {
  unsigned int n_connex = 0; // id of the connected component
  FOREACH(list, lconnex, lcomponents) {
    if (gen_in_list_p(vtx, lconnex)) {
      break; // to pick the right connected component
    }
    // v does not belong to this connected component
    n_connex++;
  }
  return (n_connex == gen_length(lcomponents)) ? -1 : (int)n_connex;
}

static list sigmac_get_component_outputs(list lconnex, dag dg) {
  list result = NIL;
  bool output;
  FOREACH(dagvtx, vtx, lconnex) {
    output = false;
    if (!gen_length(dagvtx_succs(vtx)) || gen_in_list_p(vtx, dag_outputs(dg)))
      output = true;
    FOREACH(dagvtx, succ, dagvtx_succs(vtx))
    if (!gen_in_list_p(succ, lconnex))
      output = true;
    if (output)
      result = CONS(dagvtx, vtx, result);
  }
  return result;
}

static list sigmac_get_component_inputs(list lconnex, dag dg) {
  list result = NIL;
  bool input;
  FOREACH(dagvtx, v, lconnex) {
    input = false;
    if (!gen_length(dag_vertex_preds(dg, v)))
      input = true;
    FOREACH(dagvtx, pred, dag_vertex_preds(dg, v))
    if (!gen_in_list_p(pred, lconnex))
      input = true;
    if (input)
      result = CONS(dagvtx, v, result);
  }
  return result;
}

static list sigmac_get_in_channels(list lconnex, dag dg) {
  list inputs = sigmac_get_component_inputs(lconnex, dg);
  list ext_inputs = NIL;
  FOREACH(dagvtx, vtx, inputs) {
    FOREACH(dagvtx, pred, dag_vertex_preds(dg, vtx)) {
      if (!gen_in_list_p(pred, lconnex) && !gen_in_list_p(pred, ext_inputs))
        ext_inputs = CONS(dagvtx, pred, ext_inputs);
    }
  }
  return ext_inputs;
}

static list sigmac_get_mergeable_ops(dag dg) {
  _int nb_cc = 0; // counts the connex composants
  hash_table ht_merge = hash_table_make(hash_pointer, 16);

  FOREACH(dagvtx, vtx, dag_vertices(dg)) {
    const freia_api_t *api = get_freia_api_vtx(vtx);
    if (api->sigmac.mergeable && !has_vtx_dynamic_params(vtx)) {
      // search for mergeable vtx among successors
      bool connex = false;
      FOREACH(dagvtx, succ, dagvtx_succs(vtx)) {
        if (get_freia_api_vtx(succ)->sigmac.mergeable &&
            !has_vtx_dynamic_params(succ))
          connex = true;
      }
      if (!connex)
        nb_cc++;
      hash_put(ht_merge, vtx, (void *)nb_cc);
    }
  }

  unsigned int min_thr = 2;
  unsigned int max_thr = get_int_property("HWAC_SIGMAC_MERGE_ARITH");

  // filter hash_table:
  // remove connex composants containing less than n vtx
  set set_connex[nb_cc];
  for (int i = 0; i < nb_cc; i++)
    set_connex[i] = set_make(set_pointer);

  HASH_FOREACH(dagvtx, v, _int, i, ht_merge) {
    set_add_element(set_connex[i - 1], set_connex[i - 1], v);
  }
  hash_table_free(ht_merge);

  list lresult = NIL;

  for (int i = 0; i < nb_cc; i++) {
    unsigned int p = set_size(set_connex[i]); // TODO use weight
    unsigned int g = (p + max_thr - 1) / max_thr;
    unsigned int thr = (g > 0) ? p / g + (p % g > 0) : 0;
    thr = (thr > 1) ? thr : max_thr;
    if (p >= min_thr) {
      list lconnex = NIL;

      FOREACH(dagvtx, v, dag_vertices(dg)) {
        if (set_belong_p(set_connex[i], v)) {
          if (gen_length(lconnex) == thr) {
            lresult = CONS(list, lconnex, lresult);
            lconnex = NIL;
          }
          lconnex = CONS(dagvtx, v, lconnex);
        }
      }
      if (gen_length(lconnex) >= min_thr)
        lresult = CONS(list, lconnex, lresult);
    }
  }
  return lresult;
}

static int ncompound = 0;

static void sigmac_generate_compound_agent(string_buffer sb, list lconnex,
                                           int n_connex, dag dg) {
  list outputs = sigmac_get_component_outputs(lconnex, dg);
  list ext_inputs = sigmac_get_in_channels(lconnex, dg);
  unsigned int n_inputs = gen_length(ext_inputs);
  unsigned int n_outputs = gen_length(outputs);
  sb_prf(sb, "AGENT_MERGE_ARITH(agent_compound_%d_%d, " PIXEL_T, ncompound,
         n_connex);
  sb_prf(sb, ", %d, %d, \n", n_inputs, n_outputs);

  // print input assignments
  unsigned int i;
  for (i = 0; i < n_inputs; i++)
    sb_prf(sb, "  " PIXEL_T " pi%d = inp[%d][i];\n", i, i);

  // print calls to operations
  int vtxn = 0;
  FOREACH(dagvtx, vtx, lconnex) {
    const freia_api_t *api = get_freia_api_vtx(vtx);
    string op = strdup(api->sigmac.inst_prefix);
    sb_prf(sb, "  " PIXEL_T " po%d = ", vtxn++);
    sb_prf(sb, "PIXEL_%s(", strupper(op, api->sigmac.inst_prefix));

    i = 0;
    FOREACH(dagvtx, pred, dag_vertex_preds(dg, vtx)) {
      if (gen_in_list_p(pred, lconnex)) {
        sb_prf(sb, "po%d", gen_position(pred, lconnex) - 1);
      } else {
        // use pi%d variables
        sb_prf(sb, "pi%d", gen_position(pred, ext_inputs) - 1);
      }
      if (i < gen_length(dag_vertex_preds(dg, vtx)) + api->arg_misc_in - 1)
        sb_cat(sb, ", ");
      i++;
    }

    // get misc param values
    hash_table hparams = hash_table_make(hash_pointer, 0);
    int nparams = 0;
    list vtx_param_vals = sc_get_params_values(vtx, hparams, &nparams);

    // print param values
    i = 0;
    FOREACH(expression, arg, vtx_param_vals) {
      sb_prf(sb, "%s", expression_to_string(arg));
      if (i < api->arg_misc_in - 1)
        sb_cat(sb, ", ");
      i++;
    }

    sb_prf(sb, ");\n");
    hash_table_free(hparams);
  }

  // print output assignments
  i = 0;
  FOREACH(dagvtx, vtx, outputs) {
    sb_prf(sb, "  outp[%d][i] = po%d;\n", i++, gen_position(vtx, lconnex) - 1);
  }

  sb_cat(sb, ");\n"
             "\n");

  gen_free_list(outputs);
  gen_free_list(ext_inputs);
}

/*
 */
static list get_succ_insts(dagvtx vtx, list lcomponents, dag dg,
                           hash_table htid) {
  list res = NIL;
  string_buffer succ_inst = string_buffer_make(true);
  int vtxconnex = is_vtx_compound(vtx, lcomponents);
  list used_components = NIL;

  FOREACH(dagvtx, succ, dagvtx_succs(vtx)) {
    _int succconnex = is_vtx_compound(succ, lcomponents);
    if (vtxconnex != -1 && succconnex == vtxconnex)
      continue;

    else if (succconnex == -1) { // add succ
      sb_prf(succ_inst, "%s.input", sc_vtx_tostring(succ, htid));
      if (get_freia_api_vtx(succ)->arg_img_in > 1)
        sb_prf(succ_inst, "[%d]", sc_get_port_id(vtx, succ, dg));
    }

    else if (succconnex != -1) {
      // add corresponding compound agent if not already connected
      if (!gen_in_list_p((void *)succconnex, used_components)) {
        used_components = CONS(int, succconnex, used_components);
        sb_prf(
            succ_inst, "cpd%"_intFMT
                       ".input[%d]",
            succconnex,
            gen_position(vtx, sigmac_get_in_channels(
                                  LIST(gen_nth(succconnex, lcomponents)), dg)) -
                1);
      }
    }
    if (!string_buffer_empty_p(succ_inst))
      res = CONS(string, string_buffer_to_string(succ_inst), res);
    string_buffer_reset(succ_inst);
  }

  if (gen_in_list_p(vtx, dag_outputs(dg))) { // add strout.input[%d]
    sb_prf(succ_inst, "strout.input[%d] /* %s */",
           gen_position(vtx, dag_outputs(dg)) - 1,
           expression_to_string(entity_to_expression(dagvtx_image(vtx))));
    res = CONS(string, string_buffer_to_string(succ_inst), res);
  }

  string_buffer_free(&succ_inst);
  return res;
}

static void sigmac_compile_subgraph(string module, dag dg, string fname,
                                    int n_split, FILE *helper) {
  fprintf(helper, "// code module=%s fname=%s split=%d\n", module, fname,
          n_split);

  /*
   * Variables used for SigmaC code generation
   */

  string_buffer sb = string_buffer_make(true);
  string_buffer sb_new = string_buffer_make(true);
  string_buffer sb_conn = string_buffer_make(true);
  string_buffer sb_par = string_buffer_make(true);
  string_buffer sb_cpd = string_buffer_make(true);
  string_buffer sb_mor = string_buffer_make(true);

  // stores vtx instance id
  hash_table htid = hash_table_make(hash_pointer, 16);
  // get a name for each vertex
  sigmac_name_instances(dg, htid);

  // stores dagvtx parameters
  hash_table hparams = hash_table_make(hash_pointer, 0);
  int nparams = 0;
  // declare dag constant parameters
  sigmac_params_decl(sb_par, dg, hparams, &nparams);

  // detect mergeable arithmetic components
  list lcomponents = NIL;
  if (get_int_property("HWAC_SIGMAC_MERGE_ARITH"))
    lcomponents = sigmac_get_mergeable_ops(dg);
  _int n_connex = 0;
  // instiantiate the compound agents
  FOREACH(list, lconnex, lcomponents) {
    sigmac_generate_compound_agent(sb_cpd, lconnex, n_connex++, dg);
  }
  list lcomponents_inst = NIL;

  // generate kernel specific morphological agents
  if (get_bool_property("HWAC_SIGMAC_SPECIFIC_MORPHO"))
    sc_kernel_specific_agent(sb_mor, hparams, dg);

  // some counters...
  int nb_rep_nd = 0;    // number of dup agents
  int join_port_n = 0;  // number of reduction scalar results
  int split_port_n = 0; // number of dynamic parameters

  pips_assert("image size must be available",
              get_int_property("FREIA_IMAGE_WIDTH") &&
                  get_int_property("FREIA_IMAGE_HEIGHT"));

  /* Main loop
   * looping over the list of vertices of the given dag
   */
  FOREACH(dagvtx, v, dag_vertices(dg)) {

    const freia_api_t *f = get_freia_api_vtx(v);

    // test if current vtx part of one compound agent
    n_connex = is_vtx_compound(v, lcomponents);

    // test if current vtx has dynamic parameters
    bool dynamic_agent = has_vtx_dynamic_params(v);

    // instantiate current vtx - filter out input vtx
    if (!same_string_p(dagvtx_operation(v), "undefined")) {
      if (n_connex == -1) {
        // if not compound, instantiate current dagvtx agent normally
        if (dagvtx_is_measurement_p(v))
          sc_inst(sb_new, v, htid, NULL, NULL, dynamic_agent);
        else
          sc_inst(sb_new, v, htid, hparams, NULL, dynamic_agent);
      } else { // if compound, only instantiate once
        if (!gen_in_list_p((void *)n_connex, lcomponents_inst)) {
          sb_prf(sb_new,
                 SIGMAC_INSTANTIATE("cpd%d", "agent_compound_%d_%d(width)"),
                 n_connex, ncompound, n_connex);
          lcomponents_inst = CONS(int, n_connex, lcomponents_inst);
        }
      }
    }

    // manipulate more easily instname.output
    string_buffer sb_instoutp = string_buffer_make(true);
    if (gen_in_list_p(v, dag_inputs(dg)))
      sb_prf(sb_instoutp, "strin.output[%d] /* %s */",
             gen_position(v, dag_inputs(dg)) - 1,
             expression_to_string(entity_to_expression(dagvtx_image(v))));
    else if (n_connex == -1)
      sb_prf(sb_instoutp, "%s.output", sc_vtx_tostring(v, htid));
    else {
      list comp_outps = sigmac_get_component_outputs(
          LIST(gen_nth(n_connex, lcomponents)), dg);
      sb_prf(sb_instoutp, "cpd%d.output[%d]", n_connex,
             gen_position(v, comp_outps) - 1);
    }
    string instoutp = string_buffer_to_string(sb_instoutp);
    string_buffer_free(&sb_instoutp);

    // deal with measure agents: connect to join
    if (dagvtx_is_measurement_p(v)) {
      unsigned int i;
      if (f->arg_misc_out == 1)
        sb_prf(sb_conn, SIGMAC_CONNECT("%s", "jo.input[%d]"), instoutp,
               join_port_n++);
      else if (f->arg_misc_out > 1)
        for (i = 0; i < f->arg_misc_out; i++)
          sb_prf(sb_conn, SIGMAC_CONNECT("%s[%d]", "jo.input[%d]"), instoutp, i,
                 join_port_n++);
    }

    // deal with dynamic parameter dagvtx: connect to split
    if (dynamic_agent) {
      unsigned int i;
      for (i = 0; i < f->arg_misc_in; i++) {
        string s = "";
        if (dagvtx_optype(v) == spoc_type_thr)
          s = strdup(cat("[", i2a(i), "]"));
        sb_prf(sb_conn, SIGMAC_CONNECT("sp.output[%d]", "%s.param%s"),
               split_port_n++, sc_vtx_tostring(v, htid), s);
      }
    }

    // connect current vtx to its succs
    list succ_insts = get_succ_insts(v, lcomponents, dg, htid);
    if (gen_length(succ_insts) > 1) {
      FOREACH(string, inst, succ_insts) {
        sb_prf(sb_conn, SIGMAC_CONNECT("dup%d.output[%d]", "%s"), nb_rep_nd,
               gen_position(inst, succ_insts) - 1, inst);
      }
      sb_prf(sb_conn, SIGMAC_CONNECT("%s", "dup%d.input"), instoutp, nb_rep_nd);
      sb_prf(sb_new,
             SIGMAC_INSTANTIATE("dup%d", REPLICATION_AGENT "(%d, width)"),
             nb_rep_nd, gen_length(succ_insts));
      nb_rep_nd++;
    } else {                              // gen_length(succ_insts) <= 1
      FOREACH(string, inst, succ_insts) { // auto cast to string
        sb_prf(sb_conn, SIGMAC_CONNECT("%s", "%s"), instoutp, inst);
      }
    }

  } // FOREACH(dagvtx, v, dg)

  string subgraph_name = strdup(cat(fname, "_", i2a(n_split)));
  sc_delimiter(sb, strdup(cat(subgraph_name, " Subgraph")));

  // compound agent declaration
  sb_cat(sb, string_buffer_to_string(sb_cpd));

  // kernel specific morpho agent declaration
  sb_cat(sb, string_buffer_to_string(sb_mor));

  // subgraph header and pipe agents declaration
  sc_subgraph_app(sb, subgraph_name, gen_length(dag_inputs(dg)),
                  gen_length(dag_outputs(dg)), split_port_n, join_port_n);

  // append the parameter declarations
  sb_cat(sb, "\n    // parameters declaration...\n");
  sb_cat(sb, string_buffer_to_string(sb_par));

  // append the instantiation statements in reverse order
  sb_cat(sb_new, "    // instantiations...\n");
  sb_cat(sb_new, "\n");
  sb_cat(sb, string_buffer_to_string_reverse(sb_new));
  sb_cat(sb, "\n");

  // append the connection statements
  sb_cat(sb_conn, "    // connections...\n");
  sb_cat(sb, string_buffer_to_string_reverse(sb_conn));
  sb_cat(sb, "  }\n}\n");

  string_buffer_to_file(sb, helper);
  fprintf(helper, "\n");

#ifdef DEBUG_INFO
  FOREACH(dagvtx, v, dag_vertices(dg)) {
    fprintf(helper, "vtx %"_intFMT
                    ", op %s,",
            dagvtx_number(v), dagvtx_operation(v));
    dagvtx_nb_dump(helper, " succs", dagvtx_succs(v));
  }
  dag_dump(helper, "hello", dg);
#endif

  ncompound++;
  /*
   * Memory cleanup
   */
  string_buffer_free(&sb);
  string_buffer_free(&sb_new);
  string_buffer_free(&sb_conn);
  string_buffer_free(&sb_par);
  string_buffer_free(&sb_cpd);
  string_buffer_free(&sb_mor);

  hash_table_free(htid);
  hash_table_free(hparams);

  FOREACH(list, lconnex, lcomponents)
  gen_free_list(lconnex);
  gen_free_list(lcomponents);
}

#define SIGMAC_HELPER "freia_mppa_launch"

/* call this helper for dag d
 * ??? currently non constant parameters are NOT handled at all.
 */
static void sigmac_call_helper(dag d, int helper) {
  int n_inputs = gen_length(dag_inputs(d));
  int n_outputs = gen_length(dag_outputs(d));

  list lpin = NIL;
  list lpout = NIL;

  FOREACH(dagvtx, v, dag_vertices(d)) {
    // pass dynamic arguments of *_const agents
    if (strstr(get_freia_api_vtx(v)->function_name, "_const")) {
      list vtx_params = gen_full_copy_list(freia_get_vertex_params(v));
      FOREACH(expression, paramin, vtx_params) {
        if (is_param_dynamic(paramin))
          lpin = CONS(expression, paramin, lpin);
      }
    }

    // pass arguments of thresholder_dyn agent
    if (dagvtx_optype(v) == spoc_type_thr && has_vtx_dynamic_params(v)) {
      list vtx_params = gen_full_copy_list(freia_get_vertex_params(v));
      FOREACH(expression, paramin, vtx_params) {
        lpin = CONS(expression, paramin, lpin);
      }
    }

    // return result of measure agents
    if (dagvtx_is_measurement_p(v))
      lpout = gen_nconc(lpout, gen_full_copy_list(freia_get_vertex_params(v)));
  }
  lpin = gen_nreverse(lpin);

  list largs = gen_make_list(
      expression_domain, int_to_expression(helper), int_to_expression(n_inputs),
      int_to_expression(n_outputs), int_to_expression(gen_length(lpin)),
      int_to_expression(gen_length(lpout)), NULL);
  list lin = NIL;
  FOREACH(dagvtx, v, dag_inputs(d)) {
    entity in = dagvtx_image(v);
    if (in)
      lin = CONS(expression, entity_to_expression(in), lin);
  }
  lin = gen_nreverse(lin);

  list lout = NIL;
  FOREACH(dagvtx, v, dag_outputs(d)) {
    entity out = dagvtx_image(v);
    if (out)
      lout = CONS(expression, entity_to_expression(out), lout);
  }
  lout = gen_nreverse(lout);

  largs = gen_nconc(largs, lin);
  largs = gen_nconc(largs, lout);
  largs = gen_nconc(largs, lpin);
  largs = gen_nconc(largs, lpout);

  // rough...
  bool call_inserted = false;
  FOREACH(dagvtx, v, dag_vertices(d)) {
    _int op = dagvtx_opid(v);
    if (op == 0)
      continue;
    statement st = dagvtx_statement(v);
    if (call_inserted)
      hwac_replace_statement(st, freia_ok(), true);
    else {
      entity sc_helper = local_name_to_top_level_entity(SIGMAC_HELPER);
      if (entity_undefined_p(sc_helper))
        sc_helper = freia_create_helper_function(SIGMAC_HELPER, NIL);
      hwac_replace_statement(st, make_call(sc_helper, largs), false);
      call_inserted = true;
    }
  }
}

/*#######################################################################*/
/*#######################################################################*/
/*#######################################################################*/

// global string_buffer, stores the subgraph calls
static string_buffer subg_calls;

#define N_PREDEFINED_CONTROLLERS 5

static void print_subgraph_calls(string fname, int n_split, int n_dags) {
  /* we generate an application subgraph with 4 pipes
   * for every independant dag
   */
  sb_prf(subg_calls, "    new %s_%d\n"
                     "    (pipes[%d], pipes[%d],\n"
                     "     width, height, sizeMax,\n"
                     "     pipes[%d], pipes[%d]);\n"
                     "\n",
         fname, n_split, 4 * n_dags + 2 * N_PREDEFINED_CONTROLLERS,
         4 * n_dags + 2 * N_PREDEFINED_CONTROLLERS + 1,
         4 * n_dags + 2 * N_PREDEFINED_CONTROLLERS + 2,
         4 * n_dags + 2 * N_PREDEFINED_CONTROLLERS + 3);
}

#define MAIN_PATH "cd .. && ./main"

/* Generate a root subgraph (equivalent of the main function)
 * which initialize the image data
 * and calls the application subgraphs
 */
static void sc_subgraph_root(FILE *sigmac_helper, int n_graphs) {
  string_buffer sb = string_buffer_make(true);
  sc_delimiter(sb, "Subgraph Root");

  sb_prf(sb, "subgraph root () {\n"
             "  map {\n"
             "    int width = %d, height = %d;\n"
             "    size_t sizeMax = width * height * sizeof(" PIXEL_T ");\n"
             "\n",
         get_int_property("FREIA_IMAGE_WIDTH"),
         get_int_property("FREIA_IMAGE_HEIGHT"));

  string exec_path = MAIN_PATH;
  sb_cat(sb, "    char cmd[255] = \"", exec_path, "\";\n");

  /* two i/o pipes for each predefined controller and
   * four for each dag (2 for images i/o, 2 for parameters i/o)
   */
  int n_pipes = 2 * N_PREDEFINED_CONTROLLERS + 4 * n_graphs;

  sb_prf(sb, "    int i, n_pipes = %d;\n", n_pipes);
  sb_cat(sb, "    char pipes[n_pipes][255];\n"
             "    for (i=0; i<n_pipes; i++)\n"
             "      tmpnam(pipes[i]);\n"
             "\n"

             "    agent pp = new Pipes(cmd, n_pipes, pipes);\n"
             "    agent sk = new Sink<char>(1);\n"
             "    SigmaC_agent_setUnitType(sk, \"native\");\n"
             "    connect(pp.output, sk.input);\n\n"

             /* we only need one instance of the following agents
              * because several commands can be sent throughout the same pipe
              */
             "    new Malloc(pipes[0], pipes[1]);\n"
             "    new Free(pipes[2], pipes[3]);\n"
             "    new MCopy(pipes[4], pipes[5]);\n"
             "    new SendDataToMPPA(pipes[6], pipes[7], sizeMax);\n"
             "    new SendDataToHost(pipes[8], pipes[9], sizeMax);\n"
             "\n");

  // insert subgraph calls
  sb_cat(sb, string_buffer_to_string(subg_calls));
  sb_cat(sb, "  }\n}\n");

  string_buffer_to_file(sb, sigmac_helper);

  string_buffer_free(&subg_calls);
  string_buffer_free(&sb);
}

/*
  @brief compile one dag with AIPO optimizations
  @param ls statements underlying the full dag
  @param occs image occurences
  @param exchanges statements to exchange because of dependences
  @return the list of allocated intermediate images
*/
list freia_sigmac_compile_calls(string module, dag fulld, sequence sq, list ls,
                                const hash_table occs, hash_table exchanges,
                                const set output_images,
                                // for launchers...
                                __attribute__((__unused__)) FILE *helper_file,
                                __attribute__((__unused__)) set helpers,
                                int number, int n_calls) {
  pips_debug(3, "considering %d statements\n", (int)gen_length(ls));
  pips_assert("some statements", ls);

  // allocate file for sigmac stuff
  string sigmac_file_name = helper_file_name(module, "sc");
  FILE *sigmac_file = safe_fopen(sigmac_file_name, "a");

  // SigmaC includes
  if (n_dags == 0) {
    fprintf(sigmac_file, FREIA_SIGMAC_SC_INCLUDES);
    subg_calls = string_buffer_make(true);
  }

  // intermediate images
  hash_table init = hash_table_make(hash_pointer, 0);
  list new_images = dag_fix_image_reuse(fulld, init, occs);

  // about aipo statistics: no helper file to put them...
  list added_before = NIL, added_after = NIL;
  freia_dag_optimize(fulld, exchanges, &added_before, &added_after);

  // dump final optimised dag
  dag_dot_dump_prefix(module, "dag_cleaned_", number, fulld, added_before,
                      added_after);

  string fname_fulldag = strdup(cat(module, "_sigmac", HELPER, i2a(number)));

  list ld = dag_split_on_scalars(fulld, NULL, NULL,
                                 (gen_cmp_func_t)dagvtx_sigmac_priority, NULL,
                                 output_images);

  pips_debug(3, "dag initial split in %d dags\n", (int)gen_length(ld));

  int n_split = 0;

  set stats = set_make(set_pointer), dones = set_make(set_pointer);

  FOREACH(dag, d, ld) {
    if (dag_no_image_operation(d))
      continue;

    // fix statements connexity
    dag_statements(stats, d);
    freia_migrate_statements(sq, stats, dones);
    set_union(dones, dones, stats);

    // helper_file?
    sigmac_compile_subgraph(module, d, fname_fulldag, n_split, sigmac_file);
    print_subgraph_calls(fname_fulldag, n_split, n_dags);
    sigmac_call_helper(d, n_dags);

    n_split++;
    n_dags++;
  }

  // generate the subgraph root which will launch the application
  if (number == n_calls - 1)
    sc_subgraph_root(sigmac_file, n_dags);

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
  fclose(sigmac_file);
  free(sigmac_file_name);

  return reals;
}
