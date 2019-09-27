/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>
#include <util/options.h>

#include "strategy_solver_base.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "linrank_domain.h"
#include "equality_domain.h"
#include "lexlinrank_domain.h"
#include "predabs_domain.h"
#include "template_generator_ranking.h"
#include "ssa_analyzer.h"
#include "strategy_solver_heap_tpolyhedra.h"
#include "strategy_solver_heap_tpolyhedra_sympath.h"
#include "strategy_solver.h"

// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
#if 0
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch2t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch3t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA, SSA.ns)
#endif


// CPROVER prefix and its length
#define CPROVER_PRFX "__CPROVER_"
#define CPROVER_PRFX_LEN 10

// dynamic objects prefix and its length
#define DYN_PRFX "dynamic_object$"
#define DYN_PRFX_LEN 15

// loop back string and its length
#define LPB_STR "#lb"
#define LPB_STR_LEN 3

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::operator()(
  incremental_solvert &solver,
  local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  if(SSA.goto_function.body.instructions.empty())
    return;

  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  // add precondition (or conjunction of asssertion in backward analysis)
  solver << precondition;

  domain=template_generator.domain();

  // get strategy solver from options
  strategy_solver_baset *s_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
    if(template_generator.options.get_bool_option(
         "monolithic-ranking-function"))
    {
    s_solver=new strategy_solvert(
      *static_cast<linrank_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new linrank_domaint::templ_valuet();
    }
    else
    {
    s_solver=new strategy_solvert(
      *static_cast<lexlinrank_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new lexlinrank_domaint::templ_valuet();
    }
  }
  else if(template_generator.options.get_bool_option("equalities"))
  {
    s_solver=new strategy_solvert(
      *static_cast<equality_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new equality_domaint::equ_valuet();
  }
  else if(template_generator.options.get_bool_option("heap"))
  {
    s_solver=new strategy_solvert(
      *static_cast<heap_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new heap_domaint::heap_valuet();
  }
  else if(template_generator.options.get_bool_option("heap-interval")
          || template_generator.options.get_bool_option("heap-zones"))
  {
    if(template_generator.options.get_bool_option("sympath"))
    {
      s_solver=new strategy_solver_heap_tpolyhedra_sympatht(
        *static_cast<heap_tpolyhedra_sympath_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=
        new heap_tpolyhedra_sympath_domaint::heap_tpolyhedra_sympath_valuet();
    }
    else
    {
      s_solver=new strategy_solver_heap_tpolyhedrat(
        *static_cast<heap_tpolyhedra_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new heap_tpolyhedra_domaint::heap_tpolyhedra_valuet();
    }
  }
  else
  {
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      s_solver=new strategy_solvert(
        *static_cast<tpolyhedra_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new tpolyhedra_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("predabs-solver"))
    {
      s_solver=new strategy_solvert(
        *static_cast<predabs_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new predabs_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))	
    {
      result=new tpolyhedra_domaint::templ_valuet();
      s_solver=new BINSEARCH_SOLVER;
    }
    else
      assert(false);
  }

  s_solver->set_message_handler(get_message_handler());

  // initialize inv
  domain->initialize(*result);

  // iterate
  while(s_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=s_solver->get_number_of_solver_instances();
  solver_calls+=s_solver->get_number_of_solver_calls();
  solver_instances+=s_solver->get_number_of_solver_instances();

  // imprecision identification 
  if(template_generator.options.get_bool_option("show-imprecise-vars"))
  {
    // get imprecise SSA variable names
    std::vector<std::string> ssa_vars=
      domain->identify_invariant_imprecision(*result);

    // link the variables to the exact goto instuctions
    find_goto_instrs(SSA, ssa_vars);
  }

  delete s_solver;
}

/*******************************************************************\

Function: ssa_analyzert::get_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_result(exprt &_result, const domaint::var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}

/*******************************************************************\

Function: ssa_analyzert::update_heap_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void ssa_analyzert::update_heap_out(summaryt::var_sett &out)
{
  heap_domaint &heap_domain=static_cast<heap_domaint &>(*domain);

  auto new_heap_vars=heap_domain.get_new_heap_vars();
  out.insert(new_heap_vars.begin(), new_heap_vars.end());
}

/*******************************************************************\

Function: ssa_analyzert::input_heap_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
const exprt ssa_analyzert::input_heap_bindings()
{
  return static_cast<heap_domaint &>(*domain).get_iterator_bindings();
}

/*******************************************************************\

Function: ssa_analyzert::find_goto_instrs

  Inputs: Local SSA, vector of imprecise SSA loop back variable names

 Outputs: 

 Purpose: Save the source code information about the variables into 
          the summary of imprecise variables

\*******************************************************************/
void ssa_analyzert::find_goto_instrs(
  local_SSAt &SSA, 
  std::vector<std::string> &ssa_vars)
{
  // reserve space in the summary for all the variables
  vars_summary.resize(ssa_vars.size());
  imprecise_varst::iterator summary_it=vars_summary.begin();

  for (auto &var : ssa_vars)
  {
    // skip CPROVER variables i.e., have "__CPROVER_" prefix
    if (var.compare(0, CPROVER_PRFX_LEN, CPROVER_PRFX)==0)
      continue;

    // dynamic variables have "dynamic_object$" prefix
    bool is_dynamic=((var.compare(0, DYN_PRFX_LEN, DYN_PRFX))==0);

    // save the pretty name of variables into the summary
    if (is_dynamic)
      summary_it->pretty_name=get_dynobj_name(var);
    else
      summary_it->pretty_name=get_pretty_name(var);

    // get the node location of a variable in local SSA 
    int node_loc=get_name_node_loc(var);

    // is not loop back variable -> 
    //  location of the node in the local SSA is unknown
    if (node_loc==-1)
      continue;

    // get the actual loop back node in the local SSA 
    local_SSAt::nodest::iterator lb_node=
      SSA.find_node(
        SSA.get_location(static_cast<unsigned>(node_loc))
    );

    // get the loop head node of the node
    local_SSAt::nodest::iterator lh_node=lb_node->loophead;

    // save the source location of the loop head node in the summary
    summary_it->loophead_loc=lh_node->location->source_location.get_line();

    // for dynamic objects additionally we save:
    //  allocation site location
    //  if structured-typed -> its structure field
    if (is_dynamic)
    {
      int site_node_loc=get_alloc_site_node_loc(var);

      // location could not be parsed from its name
      if (site_node_loc==-1)
        summary_it->dyn_alloc_loc="<NOT FOUND>";
      else
      {
        // save the source location of the allocation site
        summary_it->dyn_alloc_loc=(
          SSA.find_node(
            SSA.get_location(static_cast<unsigned>(site_node_loc))
        ))->location->source_location.get_line();
      }

      summary_it->dyn_mem_field=get_dynamic_field(var);
    }

    summary_it++;
  }
}

/*******************************************************************\

Function: ssa_analyzert::get_dynobj_name(const std::string &name)

  Inputs: SSA loop-back Dynamic object name

 Outputs: SSA dynamic object name without its field and anything after

 Purpose: Get only the dynamic object name: "dynamic_object$i#y"

\*******************************************************************/
std::string ssa_analyzert::get_dynobj_name(const std::string &name)
{
  size_t idx;

  // is structure-typed object -> 
  //  get the part right before the object field
  if ((idx=name.find('.', DYN_PRFX_LEN))!=std::string::npos)
    return name.substr(0, idx);
  // remove everything after loop back part of the string
  else if ((idx=name.rfind(LPB_STR))!=std::string::npos)
    return name.substr(0, idx);
  else
    return name;
}

/*******************************************************************\

Function: ssa_analyzert::get_pretty_name(const std::string &name)

  Inputs: SSA loop-back variable name.

 Outputs: Pretty name of the SSA variable (only the part before '#').

 Purpose: Strip the name of the part after '#' (including the '#').

\*******************************************************************/
std::string ssa_analyzert::get_pretty_name(const std::string &name)
{
  size_t idx=name.find('#');

  // is already the 'pretty' variable name
  if(idx==std::string::npos)
    return name;

  return name.substr(0, idx);
}

/*******************************************************************\

Function: ssa_analyzert::get_name_node_loc(const std::string &name)

  Inputs: SSA loop back variable name.

 Outputs: Location of the node in the local SSA.

 Purpose: Extract the node location from its ssa name.

\*******************************************************************/
int ssa_analyzert::get_name_node_loc(const std::string &name)
{
  // find last occurnce of "#lb"
  size_t idx=name.rfind(LPB_STR);

  // is not a loop back variable -> has unknown location
  if(idx==std::string::npos)
    return -1;

  // get the location number after '#lb'
  std::string loc_str=name.substr(idx+LPB_STR_LEN);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

/*******************************************************************\

Function: ssa_analyzert::get_alloc_site_node_loc(const std::string &name)

  Inputs: SSA loop back dynamic variable name.

 Outputs: Location of the allocation site node in the local SSA.

 Purpose: Extract the allocation site node location from its SSA name.

\*******************************************************************/
int ssa_analyzert::get_alloc_site_node_loc(const std::string &name)
{
  size_t field_pos=DYN_PRFX_LEN-1;
  if (name[field_pos]!='$')
    return -1;

  std::string loc_str=name.substr(field_pos+1);
  return std::stoi(loc_str);
}

/*******************************************************************\

Function: ssa_analyzert::get_dynamic_field(const std::string &name)

  Inputs: SSA loop back dynamic object name.

 Outputs: Structure field name of the dynamic object.

 Purpose: Extract the member field from the dynamic object name.

\*******************************************************************/
std::string ssa_analyzert::get_dynamic_field(const std::string &name)
{
  std::string not_found("<NO MEMBER>");

  // extract the '_FIELD_' in "dynamic_object$i#k._FIELD_#"
  size_t dot_pos=name.find('.', DYN_PRFX_LEN);
  if (dot_pos!=std::string::npos)
  {
    size_t hash_pos=name.find('#', dot_pos+1);
    if (hash_pos!=std::string::npos)
    {
      std::string field_str=name.substr(dot_pos+1, hash_pos-dot_pos-1);
      if (!field_str.empty())
        return field_str;
    }
  }

  return not_found;
}
