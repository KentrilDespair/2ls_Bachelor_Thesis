/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

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

#define ODebug(fmt) do {								\
	std::cerr << __FILE__ << ":" << __LINE__ << ":" << 	\
	__FUNCTION__ << "():" << fmt << "\n"; } while(0)	

#define debug() (std::cerr)

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

  ODebug("DOmain: ");
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
    if(template_generator.options.get_bool_option("enum-solver"))//> TODO HERE
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
    else if(template_generator.options.get_bool_option("binsearch-solver"))	//> TODO HERE
    {
		ODebug("Binsearch-solver new templ_valuet");
      result=new tpolyhedra_domaint::templ_valuet();
      s_solver=new BINSEARCH_SOLVER;
    }
    else
      assert(false);
  }

  s_solver->set_message_handler(get_message_handler());

  // initialize inv
  ODebug("Solver INITIALIZE domain");
  domain->initialize(*result);

  ODebug("Solver - OUTPUTTING SSA");
  SSA.output(std::cout);

  // iterate
  while(s_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=s_solver->get_number_of_solver_instances();
  solver_calls+=s_solver->get_number_of_solver_calls();
  solver_instances+=s_solver->get_number_of_solver_instances();

  // TODO TODO TODO ---------------------------------------------------

  // getting ssa vars identifs and locations
  std::vector<std::pair<unsigned, std::string>> ssa_vars_locs;

  domain->identify_invariant_imprecision(*result, ssa_vars_locs);
  // pass only necessary stuff and not big TODO
  find_goto_instrs(SSA, ssa_vars_locs);

  // ------------------------------------------------------------------

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
	ODebug("Getting result... HERE");
  // TODO
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

  Inputs: TODO

 Outputs: TODO

 Purpose: TODO

\*******************************************************************/
void ssa_analyzert::find_goto_instrs(
  local_SSAt &SSA, 
  std::vector<std::pair<unsigned, std::string>> &ssa_vars_locs)
{
  // for each variable at location in SSA
  for (auto it=ssa_vars_locs.begin(); it!=ssa_vars_locs.end(); it++)
  {
    // get SSA node on that location - end of the loop for loop back var
    local_SSAt::nodest::iterator a_it=SSA.find_node(
      SSA.get_location(it->first));

    // statement on location of loop back jump
    // debug() << "Statement: " 
    //  << from_expr(SSA.ns, "", *(a_it->equalities.begin())) << "\n";

    
    // get start of the loop node for that node
    local_SSAt::nodest::iterator loop_it=a_it->loophead;
    // node with the last assignment
    local_SSAt::nodest::iterator last_it; 

    // starting after the loophead, should never be end TODO
    loop_it++;  

    // looping through each node in the loop
    while (loop_it!=a_it)
    {
      // TODO equalities only
      for (local_SSAt::nodet::equalitiest::const_iterator e_it=
          loop_it->equalities.begin(); e_it!=loop_it->equalities.end();
          e_it++)
      {
        // debug() << "(LOOP) " << from_expr(SSA.ns,"",e_it->lhs()) << "\n";

        // get the SSA variable identifier on the left-hand side
        std::string var_lhs=from_expr(SSA.ns, "", e_it->lhs());

        // skip any guards, conditions, ... starting with '$'
        if (var_lhs[0]=='$')
          continue;

        // strip of '#'
        size_t idx=var_lhs.find('#');
        if(idx!=std::string::npos)
          var_lhs=var_lhs.substr(0, idx);

        // compare with the var 
        if (it->second==var_lhs)
        {
          debug() << "MATCH: " << from_expr(SSA.ns, "",e_it->lhs()) << "\n";
          last_it=loop_it;
        }

        // instruction at that location
        // debug() << "STAT: " << from_expr(SSA.ns, "", 
        //  loop_it->location->code); //code.get_statement() << "\n";
      }
      loop_it++;
    }

    // type of instr: should be ASSIGN
    // debug() << l_it->location->type << "\n";

    // debug() << l_it->location->code.get_statement() << "\n";
    // debug() << l_it->location->function << "\n";

    // SSA loc: 
    // debug() << l_it->location->location_number << "\n";

    debug() << "\n-> Variable \"" << it->second << "\" in ";
    debug() << last_it->location->source_location.as_string() << "\n\n";

    // debug() << l_it->location->source_location.get_line() << "\n";
    // debug() << l_it->location->source_location.get_comment() << "\n";
    // debug() << l_it->location->source_location.get_function() << "\n";
  }
}
