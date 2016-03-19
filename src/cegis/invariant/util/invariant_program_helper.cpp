#include <util/cprover_prefix.h>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/wordsize/restrict_bv_size.h>
#include <cegis/invariant/options/invariant_program.h>

void erase_target(goto_programt::instructionst &body,
    const goto_programt::targett &target)
{
  goto_programt::targett succ=target;
  assert(++succ != body.end());
  for (goto_programt::instructiont &instr : body)
  {
    for (goto_programt::targett &t : instr.targets)
      if (target == t) t=succ;
  }
  body.erase(target);
}

goto_programt::targett insert_before_preserve_labels(goto_programt &body,
    const goto_programt::targett &target)
{
  const goto_programt::targett result=body.insert_before(target);
  move_labels(body, target, result);
  return result;
}

void restrict_bv_size(invariant_programt &prog, const size_t width_in_bits)
{
  restrict_bv_size(prog.st, prog.gf, width_in_bits);
  const invariant_programt::invariant_loopst loops(prog.get_loops());
  for (invariant_programt::invariant_loopt * const loop : loops)
    restrict_bv_size(loop->guard, width_in_bits);
  restrict_bv_size(prog.assertion, width_in_bits);
}

namespace
{
const char RETURN_VALUE_IDENTIFIER[]="#return_value";
}
bool is_invariant_user_variable(const irep_idt &id, const typet &type)
{
  if (ID_code == type.id()) return false;
  const std::string &name=id2string(id);
  if (std::string::npos != name.find(RETURN_VALUE_IDENTIFIER)) return false;
  return std::string::npos == name.find(CPROVER_PREFIX);
}
