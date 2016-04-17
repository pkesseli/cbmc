#include <ansi-c/c_types.h>

#include <cegis/cegis-util/program_helper.h>

#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/create_temp_variables.h>
#include <cegis/jsa/preprocessing/default_jsa_constant_strategy.h>
#include <cegis/jsa/preprocessing/inline_user_program.h>
#include <cegis/jsa/preprocessing/remove_loop.h>
#include <cegis/jsa/preprocessing/jsa_preprocessing.h>

jsa_preprocessingt::jsa_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

jsa_preprocessingt::~jsa_preprocessingt()
{
}

namespace
{
void store_input_locations(jsa_programt &prog)
{
  goto_programt::instructionst &body=get_entry_body(prog.gf).instructions;
  const goto_programt::targett end(body.end());
  for (auto instr=body.begin(); instr != body.end(); ++instr)
    if (is_nondet(instr, end)) prog.input_locations.push_back(instr);
}
}

void jsa_preprocessingt::operator()()
{
  goto_functionst &gf=original_program.gf;
  symbol_tablet &st=original_program.st;
  inline_jsa_user_program(st, gf);
  store_input_locations(original_program);
  remove_loop(original_program);
  add_jsa_constraint_meta_variables(original_program);
  original_program.synthetic_variables=default_jsa_constant_strategy(st, gf);
  gf.update();
  current_program=original_program;
}

void jsa_preprocessingt::operator()(const size_t max_length)
{
  current_program=original_program;
  goto_functionst &gf=current_program.gf;
  create_jsa_temp_variables(current_program, max_length);
  gf.update();
}

size_t jsa_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

const jsa_programt &jsa_preprocessingt::get_jsa_program() const
{
  return current_program;
}
