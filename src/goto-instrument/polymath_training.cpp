/*******************************************************************\

Module: Polymath training

Author: Pascal Kesseli

Date: March 2024

\*******************************************************************/

/// \file
/// Polymath training

#include "polymath_training.h"

#include <util/cmdline.h>
#include <util/invariant.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

#define VALIDATE "validate"

void parse_polymath_training_options(const cmdlinet &cmdline, optionst &options)
{
  PRECONDITION(!options.is_set(POLYMATH_CONVERT_OPT));
  PRECONDITION(!options.is_set(POLYMATH_INSERT_OPT));

  const bool polymath_convert_opt = cmdline.isset(POLYMATH_CONVERT_OPT);
  const bool polymath_insert_opt = cmdline.isset(POLYMATH_INSERT_OPT);

  if(polymath_convert_opt)
  {
    options.set_option(
      POLYMATH_CONVERT_OPT, cmdline.get_values(POLYMATH_CONVERT_OPT));
  }
  if(polymath_insert_opt)
  {
    options.set_option(
      POLYMATH_INSERT_OPT, cmdline.get_value(POLYMATH_INSERT_OPT));
  }
}

/// Helper to find a \c goto_programt body by the function name.
///
/// \param goto_model: GOTO model in which to search for the function.
/// \param name: Name of the function to find.
/// \param calling_option: CLI option from which we are calling.
/// \return Body of searched function.
static goto_programt &get_function_body(
  goto_modelt &goto_model,
  const irep_idt &name,
  const char *const calling_option)
{
  auto &function_map = goto_model.goto_functions.function_map;
  auto it = function_map.find(name);
  if(cend(function_map) == it)
  {
    throw invalid_command_line_argument_exceptiont(
      "missing Polymath `" + id2string(name) + "` function",
      "--" + std::string(calling_option));
  }
  return it->second.body;
}

namespace
{
/// Helper to transform the \c validate method in a Polymath synthesis
/// constraint to a VC. Performs the following transformation in \c validate:
///
/// Original:
/// \code
/// int lhs;
/// int rhs;
/// __CPROVER_assume(lhs > 0);
/// __CPROVER_assume(rhs == lhs + 1)
/// int x;
/// ...
/// \endcode
///
/// Transformed:
/// \code
/// int lhs;
/// int rhs;
/// __CPROVER_bool __CPROVER_property_switch_0;
/// __CPROVER_assume(!__CPROVER_property_switch_0 || (lhs > 0));
/// __CPROVER_assume(!__CPROVER_property_switch_0 || (rhs == lhs + 1))
/// __CPROVER_assert(__CPROVER_property_switch_0, "")
/// int x;
/// ...
/// \endcode
///
/// This transformation allows to check individually whether each property
/// describing a valid solution is satisfiable.
class convert_validatet
{
  const irep_idt validate_name;
  symbol_tablet &symbol_table;
  goto_programt &validate;
  goto_programt::instructionst &instructions;
  goto_programt::targett current_instruction;
  const irep_idt &mode;

public:
  convert_validatet(goto_modelt &goto_model)
    : validate_name(VALIDATE),
      symbol_table(goto_model.symbol_table),
      validate(
        get_function_body(goto_model, validate_name, POLYMATH_CONVERT_OPT)),
      instructions(validate.instructions),
      current_instruction(begin(instructions)),
      mode(symbol_table.lookup_ref(validate_name).mode)
  {
  }

  /// Finds the next range of assume statements. Multiple subsequent assumptions
  /// in a Polymath synthesis constraint are treated as a single property.
  ///
  /// \return Pair if \c targett iterators, containing the next range of
  /// assumptions found in the range \c [current_instruction,end). This range of
  /// assumptions is exclusive, meaning that \c second no longer refers to an
  /// assumption.
  std::pair<goto_programt::targett, goto_programt::targett> next_assume_range()
  {
    const goto_programt::targett end_of_body = end(instructions);
    auto is_assume = std::mem_fun_ref(&goto_programt::instructiont::is_assume);
    const goto_programt::targett first =
      find_if(current_instruction, end_of_body, is_assume);

    if(first == end_of_body)
    {
      return make_pair(end_of_body, end_of_body);
    }

    current_instruction = find_if(first, end_of_body, not1(is_assume));
    if(current_instruction == end_of_body)
    {
      return make_pair(first, next(first));
    }

    return make_pair(first, current_instruction);
  }

  void operator()()
  {
    auto [first, last] = next_assume_range();
    size_t property_switch_index = 0u;
    while(first != last)
    {
      const symbolt property_switch_symbol(
        "__CPROVER_property_switch_" + std::to_string(property_switch_index++),
        bool_typet(),
        mode);
      symbol_table.add(property_switch_symbol);
      const symbol_exprt property_switch = property_switch_symbol.symbol_expr();

      for(auto it = first; it != last; ++it)
      {
        it->condition_nonconst() =
          or_exprt(not_exprt(property_switch), it->condition());
      }

      goto_programt::instructiont decl_property_switch =
        goto_programt::make_decl(property_switch, first->source_location());
      validate.insert_before_swap(first, decl_property_switch);
      const goto_programt::instructiont assert_property_switch =
        goto_programt::make_assertion(property_switch, last->source_location());
      goto_programt::targett assertion =
        validate.insert_after(last, assert_property_switch);
      validate.insert_after(
        assertion,
        goto_programt::make_dead(property_switch, last->source_location()));

      tie(first, last) = next_assume_range();
    }
  }
};

/// Helper to transform the \c main method in a Polymath synthesis
/// constraint to a VC. Performs the following transformation in \c main:
///
/// Original:
/// \code
/// struct Solution solution;
/// init_Solution(&solution);
/// validate(solution);
/// 
/// __CPROVER_output("solution", solution);
/// __CPROVER_assert(false, "");
/// \endcode
///
/// Transformed:
/// \code
/// struct Solution __CPROVER_scored_solution; // Insert solution here using --polymath-insert
/// validate(__CPROVER_scored_solution);
/// struct Solution solution;
/// init_Solution(&solution);
/// __CPROVER_assert(solution == __CPROVER_scored_solution, "");
/// \endcode
///
/// This transformation invokes \c validate on an inserted
/// __CPROVER_scored_solution to be socred in RL. It further adds an assertion
/// which is satisfiable iff \c __CPROVER_scored_solution satisfies all type
/// constraints (e.g. uniqueness of a field).
class convert_maint
{
  goto_modelt &goto_model;

public:
  convert_maint(goto_modelt &goto_model) : goto_model(goto_model)
  {
  }

  void operator()()
  {
    symbol_tablet &symbol_table = goto_model.symbol_table;
    goto_programt &main =
      get_function_body(goto_model, "main", POLYMATH_CONVERT_OPT);

    const symbolt &solution = symbol_table.lookup_ref("main::1::solution");
    const symbolt scored_solution_symbol(
      "__CPROVER_scored_solution", solution.type, solution.mode);
    symbol_table.add(scored_solution_symbol);
    const symbol_exprt scored_solution = scored_solution_symbol.symbol_expr();

    goto_programt::instructionst &instructions = main.instructions;
    goto_programt::targett target = begin(instructions);
    const source_locationt &first_loc = target->source_location();
    goto_programt::instructiont declare_scored_solution(
      goto_programt::make_decl(scored_solution, first_loc));
    main.insert_before_swap(target, declare_scored_solution);

    const symbolt &validate = symbol_table.lookup_ref(VALIDATE);
    code_function_callt::argumentst arguments = {scored_solution};
    target = main.insert_after(
      target,
      goto_programt::make_function_call(
        nil_exprt(), validate.symbol_expr(), std::move(arguments), first_loc));

    instructions.erase(
      remove_if(
        next(target),
        end(instructions),
        [&validate](const goto_programt::instructiont &instruction)
        {
          if(instruction.is_function_call())
          {
            const exprt &func = instruction.call_function();
            if(ID_symbol == func.id())
            {
              return to_symbol_expr(func).get_identifier() == validate.name;
            }
          }

          return instruction.is_other() &&
                 instruction.code().get_statement() == ID_output;
        }),
      end(instructions));

    target = find_if(
      target,
      end(instructions),
      std::mem_fun_ref(&goto_programt::instructiont::is_assert));
    if(cend(instructions) == target)
    {
      throw invalid_command_line_argument_exceptiont(
        "missing original Polymath synthesis assertion",
        "--" + std::string(POLYMATH_CONVERT_OPT));
    }
    target->condition_nonconst() =
      equal_exprt(solution.symbol_expr(), scored_solution);
  }
};
} // namespace

void polymath_training(goto_modelt &goto_model, const optionst &options)
{
  const bool should_convert = options.is_set(POLYMATH_CONVERT_OPT);
  if(should_convert)
  {
    convert_validatet convert_validate(goto_model);
    convert_validate();
    convert_maint convert_main(goto_model);
    convert_main();
  }

  const bool should_insert = options.is_set(POLYMATH_INSERT_OPT);
  (void)should_insert;
}
