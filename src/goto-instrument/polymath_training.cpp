/*******************************************************************\

Module: Polymath training

Author: Pascal Kesseli

Date: March 2024

\*******************************************************************/

/// \file
/// Polymath training

#include "polymath_training.h"

#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/expr_initializer.h>
#include <util/invariant.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/string_constant.h>

#include <goto-programs/goto_model.h>

#include <json/json_parser.h>

/// Name of the solution validation function in a Polymath synthesis constraint.
#define VALIDATE "validate"

/// Name of the symbol storing the inserted, scored solution.
#define SCORED_SOLUTION "__CPROVER_scored_solution"

void parse_polymath_training_options(const cmdlinet &cmdline, optionst &options)
{
  PRECONDITION(!options.is_set(POLYMATH_CONVERT_OPT));
  PRECONDITION(!options.is_set(POLYMATH_INSERT_OPT));
  PRECONDITION(!options.is_set(POLYMATH_LOWERCASE_OPT));

  const bool polymath_convert_opt = cmdline.isset(POLYMATH_CONVERT_OPT);
  const bool polymath_insert_opt = cmdline.isset(POLYMATH_INSERT_OPT);
  const bool polymath_lowercase_opt = cmdline.isset(POLYMATH_LOWERCASE_OPT);

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
  if(polymath_lowercase_opt)
  {
    options.set_option(
      POLYMATH_LOWERCASE_OPT, cmdline.get_value(POLYMATH_LOWERCASE_OPT));
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

static exprt json_to_expr(
  const namespacet &,
  const source_locationt &,
  const jsont &,
  const typet &);

static array_exprt json_to_array_expr(
  const namespacet &ns,
  const source_locationt &loc,
  const json_arrayt &json_array,
  const array_typet &type)
{
  const typet &element_type = type.element_type();
  array_exprt::operandst operands;
  for(const jsont &element : json_array)
  {
    operands.emplace_back(json_to_expr(ns, loc, element, element_type));
  }
  return array_exprt(operands, type);
}

static struct_exprt json_to_struct_expr(
  const namespacet &ns,
  const source_locationt &loc,
  const json_objectt &json_object,
  const struct_tag_typet &type)
{
  struct_exprt struct_expr =
    to_struct_expr(zero_initializer(type, loc, ns).value());
  const struct_typet &struct_type = ns.follow_tag(type);
  for(const struct_typet::componentt &component : struct_type.components())
  {
    if(component.get_is_padding())
    {
      continue;
    }

    const irep_idt &id = component.get_name();
    const std::string &name = id2string(id);
    const typet &component_type = component.type();
    exprt &value = struct_expr.component(name, ns);
    value = json_to_expr(ns, loc, json_object[id2string(name)], component_type);
  }
  return struct_expr;
}

static exprt json_to_expr(
  const namespacet &ns,
  const source_locationt &loc,
  const jsont &json,
  const typet &type)
{
  const irep_idt &type_id = type.id();
  if(ID_struct_tag == type_id)
  {
    return json_to_struct_expr(
      ns, loc, to_json_object(json), to_struct_tag_type(type));
  }
  if(ID_array == type_id)
  {
    return json_to_array_expr(
      ns, loc, to_json_array(json), to_array_type(type));
  }
  if(
    ID_signedbv == type_id || ID_unsignedbv == type_id || ID_floatbv == type_id)
  {
    return constant_exprt(to_json_number(json).value, type);
  }
  if(ID_pointer == type_id)
  {
    const pointer_typet &pointer_type = to_pointer_type(type);
    if(char_type() == pointer_type.subtype())
    {
      const std::string &value = to_json_string(json).value;
      const exprt zero = zero_initializer(c_index_type(), loc, ns).value();
      const string_constantt string_literal(value);
      return address_of_exprt(index_exprt(string_literal, zero));
    }
  }

  UNREACHABLE_BECAUSE("Property expression type: " + id2string(type_id));
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
/// __CPROVER_assume(__CPROVER_property_switch_0 || (lhs > 0));
/// __CPROVER_assume(__CPROVER_property_switch_0 || (rhs == lhs + 1))
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

  /// Finds the next range of statements belonging to one property. This is
  /// explicilty marked in Polymath using `SKIP` instructions.
  ///
  /// \return Pair if \c targett iterators, containing the instructios belonging
  /// to the next property found in the range \c [current_instruction,end). This
  /// range of assumptions is exclusive, meaning that \c second is no longer
  /// part of the property.
  std::pair<goto_programt::targett, goto_programt::targett>
  next_property_range()
  {
    const goto_programt::targett end_of_body = end(instructions);
    const goto_programt::targett first = current_instruction;
    const goto_programt::targett last = find_if(
      first,
      end_of_body,
      std::mem_fun_ref(&goto_programt::instructiont::is_skip));

    if(last == end_of_body)
    {
      return make_pair(end_of_body, end_of_body);
    }

    current_instruction = next(last);
    return make_pair(first, last);
  }

  void operator()()
  {
    auto [first, last] = next_property_range();
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
        if (it->is_assume())
        {
          it->condition_nonconst() = or_exprt(property_switch, it->condition());
        }
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

      tie(first, last) = next_property_range();
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
/// __CPROVER_assert(solution != __CPROVER_scored_solution, "");
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

  void operator()() const
  {
    symbol_tablet &symbol_table = goto_model.symbol_table;
    goto_programt &main =
      get_function_body(goto_model, ID_main, POLYMATH_CONVERT_OPT);

    const symbolt &solution = symbol_table.lookup_ref("main::1::solution");
    const symbolt scored_solution_symbol(
      SCORED_SOLUTION, solution.type, solution.mode);
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
      notequal_exprt(solution.symbol_expr(), scored_solution);
  }
};

/// Helper inserting a solution to score into the `main` function.
class insert_solutiont
{
  message_handlert &message_handler;
  goto_modelt &goto_model;
  const std::string &solution_file_name;

public:
  insert_solutiont(
    message_handlert &message_handler,
    goto_modelt &goto_model,
    const std::string &solution_file_name)
    : message_handler(message_handler),
      goto_model(goto_model),
      solution_file_name(solution_file_name)
  {
  }

  void operator()() const
  {
    goto_programt &main =
      get_function_body(goto_model, ID_main, POLYMATH_INSERT_OPT);
    goto_programt::instructionst &instructions = main.instructions;
    const irep_idt scored_solution = SCORED_SOLUTION;
    const goto_programt::targett target = find_if(
      begin(instructions),
      end(instructions),
      [&scored_solution](const goto_programt::instructiont &instruction)
      {
        return instruction.is_decl() &&
               instruction.decl_symbol().get_identifier() == scored_solution;
      });

    if(cend(instructions) == target)
    {
      throw invalid_command_line_argument_exceptiont(
        "missing local variable to store inserted solution",
        "--" + std::string(POLYMATH_INSERT_OPT));
    }

    jsont solution_json;
    if(parse_json(solution_file_name, message_handler, solution_json))
    {
      throw invalid_command_line_argument_exceptiont(
        "failed to read solution JSON file",
        "--" + std::string(POLYMATH_INSERT_OPT));
    }

    const namespacet ns(goto_model.symbol_table);
    const symbol_exprt &lhs = target->decl_symbol();
    const source_locationt &loc = target->source_location();
    const exprt rhs = json_to_expr(ns, loc, solution_json, lhs.type());
    main.insert_after(target, goto_programt::make_assignment(lhs, rhs, loc));
  }
};

/// Visitor which converts every string literal to lower case.
class lowercase_visitort : public expr_visitort
{
  /// Converts \c id to lower case, reusing \c id if it is already in lower
  /// case.
  ///
  /// \param id String to convert to lower case.
  /// \return Lower case version of \c id.
  static irep_idt to_lower(const irep_idt &id)
  {
    const std::string &value = id2string(id);
    std::string lower_value;
    bool was_modified = false;
    for(const char c : value)
    {
      const char lower_char = std::tolower(c);
      was_modified |= c != lower_char;
      lower_value.push_back(lower_char);
    }

    return was_modified ? lower_value : id;
  }

public:
  virtual void operator()(exprt &expr)
  {
    if(ID_string_constant == expr.id())
    {
      string_constantt &string_constant = to_string_constant(expr);
      string_constant.value(to_lower(string_constant.value()));
    }
  }
};

/// Converts all string literals in all expressions in the entire GOTO model to
/// lower case.
class convert_to_lowercaset
{
  goto_modelt &model;
  lowercase_visitort visitor;

public:
  convert_to_lowercaset(goto_modelt &model) : model(model)
  {
  }

  void operator()()
  {
    symbol_tablet &symbol_table = model.symbol_table;
    for(auto it = std::begin(symbol_table); it != std::end(symbol_table); ++it)
    {
      it.get_writeable_symbol().value.visit(visitor);
    }
    goto_functionst &goto_functions = model.goto_functions;
    auto &functions_map = goto_functions.function_map;
    for(auto &function : functions_map)
    {
      for(auto &instr : function.second.body.instructions)
      {
        if (instr.has_condition())
        {
          instr.condition_nonconst().visit(visitor);
        }

        goto_instruction_codet &code = instr.code_nonconst();
        for (exprt &op : code.operands())
        {
          op.visit(visitor);
        }
      }
    }
  }
};
} // namespace

void polymath_training(
  message_handlert &message_handler,
  goto_modelt &goto_model,
  const optionst &options)
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
  if(should_insert)
  {
    const std::string solution_file_name =
      options.get_option(POLYMATH_INSERT_OPT);
    insert_solutiont insert_solution(
      message_handler, goto_model, solution_file_name);
    insert_solution();
  }

  const bool should_lowercase = options.is_set(POLYMATH_LOWERCASE_OPT);
  if(should_lowercase)
  {
    convert_to_lowercaset convert_to_lowercase(goto_model);
    convert_to_lowercase();
  }
}
