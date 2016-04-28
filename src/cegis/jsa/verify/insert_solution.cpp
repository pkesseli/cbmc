#include <ansi-c/c_types.h>
#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/verify/insert_solution.h>

// XXX: Debug
#include <iostream>
// XXX: Debug

#define JSA_PRED_RESULT JSA_PREFIX "pred_result"
#define SYNC_IT "__CPROVER_jsa_synchronise_iterator"
#define MAKE_NULL "__CPROVER_jsa__internal_make_null"

namespace
{
void add_predicates(jsa_programt &prog, const jsa_solutiont::predicatest &preds)
{
  assert(!preds.empty());
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_body(gf, JSA_PRED_EXEC);
  goto_programt::instructionst &instrs=body.instructions;
  std::string pred_id_name(JSA_PRED_EXEC);
  pred_id_name+="::pred_id";
  const symbol_exprt pred_id(st.lookup(pred_id_name).symbol_expr());
  goto_programt::targett pos=body.insert_after(instrs.begin());
  declare_jsa_meta_variable(st, pos, JSA_PRED_RESULT, jsa_word_type());
  const std::string result(get_cegis_meta_name(JSA_PRED_RESULT));
  const symbol_exprt ret_val(st.lookup(result).symbol_expr());
  const goto_programt::targett end=std::next(pos);
  to_code_return(end->code).return_value()=ret_val;
  std::vector<goto_programt::targett> pred_begins;
  size_t idx=0;
  for (const jsa_solutiont::predicatest::value_type &pred : preds)
  {
    assert(!pred.empty());
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=jsa_builtin_source_location();
    const constant_exprt pred_idx_expr(from_integer(idx++, pred_id.type()));
    pos->guard=notequal_exprt(pred_id, pred_idx_expr);
    pred_begins.push_back(pos);
    pos=copy_instructions(instrs, pos, pred);
    const goto_programt::targett last_assign=std::prev(pos);
    const exprt &last_lhs=to_code_assign(last_assign->code).lhs();
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=jsa_builtin_source_location();
    pos->code=code_assignt(ret_val, last_lhs);
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=jsa_builtin_source_location();
    pos->targets.push_back(end);
  }
  assert(pred_begins.size() == preds.size());
  for (auto it=pred_begins.begin(); it != std::prev(pred_begins.end()); ++it)
  {
    const goto_programt::targett &pos=*it;
    pos->targets.push_back(*std::next(it));
  }
  pred_begins.back()->targets.push_back(end);
  body.compute_incoming_edges();
  body.compute_target_numbers();
}

void insert_invariant(const symbol_tablet &st, goto_programt &body,
    goto_programt::targett pos, const goto_programt::instructionst &prog)
{
  assert(prog.size() == 1);
  const exprt &comparison=to_code_return(prog.front().code).return_value();
  const typecast_exprt cast(comparison, c_bool_type());
  const symbol_exprt v(st.lookup(get_affected_variable(*pos)).symbol_expr());
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=jsa_builtin_source_location();
  pos->code=code_assignt(v, cast);
}

const exprt &get_iterator_arg(const codet &code)
{
  const code_function_callt &call=to_code_function_call(code);
  const code_function_callt::argumentst &args=call.arguments();
  assert(args.size() >= 3);
  return args.at(2);
}

void insert_sync_call(const symbol_tablet &st, const goto_functionst &gf,
    goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &query)
{
  if (query.empty()) return;
  const exprt &it_arg=get_iterator_arg(query.front().code);
  code_function_callt sync;
  code_function_callt::argumentst &sync_args=sync.arguments();
  sync_args.push_back(address_of_exprt(get_user_heap(gf)));
  sync_args.push_back(address_of_exprt(get_queried_heap(st)));
  sync_args.push_back(it_arg);
  sync.function()=st.lookup(SYNC_IT).symbol_expr();
  pos=insert_before_preserve_labels(body, pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  pos->code=sync;
}

void make_full_query_call(const goto_functionst &gf, goto_programt &body,
    goto_programt::targett pos, const goto_programt::instructionst &query)
{
  if (query.empty()) return;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  code_function_callt call;
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_user_heap(gf)));
  args.push_back(get_iterator_arg(query.front().code));
  pos->code=call;
}

void insert_before(goto_programt::instructionst &body,
    const goto_programt::targett &pos, const goto_programt::instructionst &prog)
{
  if (prog.empty()) return;
  copy_instructions(body, std::prev(pos), prog);
}
}

void insert_jsa_solution(jsa_programt &prog, const jsa_solutiont &solution)
{
  add_predicates(prog, solution.predicates);
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);

  // XXX: Debug
  const namespacet ns(st);
  goto_programt tmp;
  tmp.instructions=solution.invariant;
  tmp.compute_incoming_edges();
  tmp.compute_target_numbers();
  std::cout << "<invariant>" << std::endl;
  tmp.output(ns, "", std::cout);
  std::cout << "</invariant>" << std::endl;
  // XXX: Debug

  goto_programt::instructionst &instrs=body.instructions;
  insert_before(instrs, prog.base_case, solution.query);
  insert_invariant(st, body, prog.base_case, solution.invariant);
  insert_before(instrs, prog.inductive_assumption, solution.query);
  insert_invariant(st, body, prog.inductive_assumption, solution.invariant);
  insert_before(instrs, prog.inductive_step, solution.query);
  insert_sync_call(st, gf, body, prog.inductive_step, solution.query);
  insert_invariant(st, body, prog.inductive_step, solution.invariant);
  make_full_query_call(gf, body, prog.property_entailment, solution.query);
  insert_before(instrs, prog.property_entailment, solution.query);
  insert_invariant(st, body, prog.property_entailment, solution.invariant);

  body.compute_incoming_edges();
  body.compute_target_numbers();
}
