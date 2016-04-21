#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/clone_heap.h>

namespace
{
bool is_heap_type(const typet &type)
{
  if (ID_symbol != type.id()) return false;
  return to_symbol_type(type).get_identifier() == JSA_HEAP_TAG;
}

bool is_heap(const goto_programt::instructiont &instr)
{
  if (goto_program_instruction_typet::DECL != instr.type) return false;
  return is_heap_type(to_code_decl(instr.code).symbol().type());
}
}

const symbol_exprt &get_user_heap_variable(const goto_functionst &gf)
{
  const goto_programt::instructionst &i=get_entry_body(gf).instructions;
  const goto_programt::const_targett end(i.end());
  const goto_programt::const_targett p=std::find_if(i.begin(), end, is_heap);
  assert(end != p);
  return to_symbol_expr(to_code_decl(p->code).symbol());
}

symbol_exprt get_cloned_heap_variable(const symbol_tablet &st)
{
  return st.lookup(get_cegis_meta_name(JSA_HEAP_CLONE)).symbol_expr();
}

void clone_heap(jsa_programt &prog)
{
  symbol_tablet &st=prog.st;
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::targett pos=prog.inductive_assumption;
  pos=insert_before_preserve_labels(body, pos);
  declare_jsa_meta_variable(st, pos, JSA_HEAP_CLONE, jsa_heap_type());
}
