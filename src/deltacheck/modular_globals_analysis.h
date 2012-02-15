/*******************************************************************\

Module: Modular (i.e., per C file) analysis of globals.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_MODULAR_GLOBALS_ANALYSIS_H
#define	CPROVER_DELTACHECK_MODULAR_GLOBALS_ANALYSIS_H

#include "modular_code_analysis.h"

class modular_globals_analysist : public modular_code_analysist {
public:
  modular_globals_analysist();
  virtual ~modular_globals_analysist();
  
  virtual const char* get_default_suffix() const
  {
    return ".dc_gl";
  }
  virtual const char* get_analysis_id() const
  {
    return "Globals analysis";
  }

  virtual void accept_assign(const code_assignt& instruction);
  virtual void accept_function_call(const code_function_callt& instruction);
  virtual void accept_return(const code_returnt& instruction);
  
  // Analysis relevant functions
  virtual bool try_compute_value(const exprt& expr, valuet& value);
  virtual bool try_compute_variable(const exprt& expr, variablet& variable);
  
  // Queries for the aliases of globals, context has to be set when calling
  bool get_aliased_globals(const irep_idt&, valuest& globals);

private:
  void process_global_dereferences_rec(const exprt& expr);
  irep_idt type_to_string(const typet& type);
};

#endif
