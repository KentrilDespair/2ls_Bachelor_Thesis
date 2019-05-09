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

// TODO prefix "dynamic_object$" string length
#define DYN_PRFX_LEN 15

// prefix "__CPROVER_" length
#define CPROVER_PRFX_LEN 10

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


  // TODO ----------------------------------------------------
  if(template_generator.options.get_bool_option("show-imprecise-vars"))
  {
    // getting imprecise ssa variables' names
    std::vector<std::string> ssa_vars=
      domain->identify_invariant_imprecision(*result);

    // printing out imprecise variables and their real locations
    find_goto_instrs(SSA, ssa_vars);
  }
  // ---------------------------------------------------------

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

  Inputs: Local SSA, vector of SSA loop back variable names

 Outputs: 

 Purpose: Map the SSA variable names back to the source program.

\*******************************************************************/
void ssa_analyzert::find_goto_instrs(
  local_SSAt &SSA, 
  std::vector<std::string> &ssa_vars)
{
  // resize the summary to the number of the variables
  vars_summary.resize(ssa_vars.size());
  imprecise_varst::iterator summary_it=vars_summary.begin();

  for (auto &var : ssa_vars)
  {
    // if verbosity - print loop-back names too TODO

    // valid names do not start with "__CPROVER_" prefix
    if (var.compare(0, CPROVER_PRFX_LEN, "__CPROVER_")==0)
      continue;

    // heap domain specific, dynamic objects, starts with string
    bool is_dynamic=((var.compare(0, DYN_PRFX_LEN, "dynamic_object$"))==0);

    // get the pretty name of the imprecise ssa var
    if (is_dynamic)
      summary_it->pretty_name=get_dynobj_name(var);
    else
      summary_it->pretty_name=get_pretty_name(var);

    // get location of the SSA var
    int loc=get_name_loc(var);

    // location could not be parsed from the variable name
    if (loc==-1)
      continue;

    // get SSA node of at "loc" - end of the loop for loop-back var
    local_SSAt::nodest::iterator lb_node=SSA.find_node(
      SSA.get_location(static_cast<unsigned>(loc)));

    // get loop-head node of that loop-back node
    local_SSAt::nodest::iterator lh_node=lb_node->loophead;

    // heap dynamic objects
    if (is_dynamic)
    {
      // adding name of the dynamic memory field
      summary_it->dyn_mem_field=get_dynamic_field(var);

      // get the object's allocation site location
      int site_loc=get_alloc_site_loc(var);

      // location could not be parsed from its name
      if (site_loc==-1)
        summary_it->dyn_alloc_loc="<NOT FOUND>";
      else
      {
        summary_it->dyn_alloc_loc=(
          SSA.find_node(
            SSA.get_location(static_cast<unsigned>(site_loc))
          ))->location->source_location.get_line();
      }
    }
    // adding location of the loop-head node
    summary_it->loophead_loc=lh_node->location->source_location.get_line();

    summary_it++;
  }
}

/*******************************************************************\

Function: ssa_analyzert::get_name_loc(const std::string &name)

  Inputs: SSA loop back variable name.

 Outputs: Location of the node in the local SSA.

 Purpose: Extract the node location from its ssa name.

\*******************************************************************/
int ssa_analyzert::get_name_loc(const std::string &name)
{
  // find last occurnce of "#lb"
  size_t idx=name.rfind("#lb");
  if(idx==std::string::npos)
    return -1;

  std::string loc_str=name.substr(idx+3);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

/*******************************************************************\

Function: ssa_analyzert::get_pretty_name(const std::string &name)

  Inputs: SSA loop-back variable name.

 Outputs: Pretty name of the SSA variable (only the part before '#').

 Purpose: Strip the name of the part after '#' (and the '#' as well).

\*******************************************************************/
std::string ssa_analyzert::get_pretty_name(const std::string &name)
{
  std::string pretty;
  size_t idx=name.find('#');

  // is already the 'pretty' variable name
  if(idx==std::string::npos)
    return name;

  pretty=name.substr(0, idx);
  return pretty;
}

/*******************************************************************\

Function: ssa_analyzert::get_dynobj_name(const std::string &name)

  Inputs: SSA loop-back Dynamic object name

 Outputs: SSA dynamic object name without its field and anything after

 Purpose: Remove its field, loop-back part and anything after in the name.

\*******************************************************************/
std::string ssa_analyzert::get_dynobj_name(const std::string &name)
{
  std::string pretty;
  size_t idx;

  // first try to remove anything after field (field included)
  if ((idx=name.find('.', DYN_PRFX_LEN))!=std::string::npos)
    pretty=name.substr(0, idx);
  // then remove anything after the start of loop-back str
  else if ((idx=name.rfind("#lb"))!=std::string::npos)
    pretty=name.substr(0, idx);
  else
    return name;

  return pretty;
}

/*******************************************************************\

Function: ssa_analyzert::get_alloc_site_loc(const std::string &name)

  Inputs: SSA loop back dynamic variable name.

 Outputs: Location of the allocation site in the local SSA.

 Purpose: Extract the allocation site location from its SSA name.

\*******************************************************************/
int ssa_analyzert::get_alloc_site_loc(const std::string &name)
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

 Outputs: Member of the dynamic object.

 Purpose: Extract the member field from the dynamic object name.

\*******************************************************************/
std::string ssa_analyzert::get_dynamic_field(const std::string &name)
{
  std::string not_found("<NO MEMBER>");

  // "dynamic_object$N.___#" <- get the '___'
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
