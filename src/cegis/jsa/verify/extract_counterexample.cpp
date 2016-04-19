#include <algorithm>

#include <util/expr_util.h>
#include <goto-programs/goto_trace.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/verify/extract_counterexample.h>

namespace
{
const typet &get_type(const symbol_tablet &st,
    const goto_programt::targett &pos)
{
  return st.lookup(get_affected_variable(*pos)).type;
}
}

void extract(const jsa_programt &prog, jsa_counterexamplet &ce,
    const goto_tracet &trace)
{
  const symbol_tablet &st=prog.st;
  const namespacet ns(st);
  null_message_handlert msg;
  const goto_programt::targetst &ce_locs=prog.counterexample_locations;
  const goto_tracet::stepst &steps=trace.steps;
  for (const goto_programt::targett &ce_loc : ce_locs)
  {
    const unsigned id=ce_loc->location_number;
    const goto_tracet::stepst::const_iterator it=std::find_if(steps.begin(),
        steps.end(), [id](const goto_trace_stept &step)
        { return step.pc->location_number == id;});
    if (steps.end() != it) ce.insert(std::make_pair(id, it->full_lhs_value));
    else
    {
      const typet &type=get_type(st, ce_loc);
      const exprt v=zero_initializer(type, ce_loc->source_location, ns, msg);
      ce.insert(std::make_pair(id, v));
    }
  }
  assert(ce.size() == prog.counterexample_locations.size());
}
