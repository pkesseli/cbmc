
// clang-format off
#define POLYMATH_CONVERT_OPT "polymath-convert"
#define POLYMATH_INSERT_OPT "polymath-insert"

#define OPT_POLYMATH \
  "(" POLYMATH_CONVERT_OPT ")" \
  "(" POLYMATH_INSERT_OPT "):"

#define HELP_POLYMATH \
  " {y--" POLYMATH_CONVERT_OPT "} \t " \
  "Transform Polymath solution synthesis constraint to an RL scorer VC template\n" \
  " {y--" POLYMATH_INSERT_OPT "} {json-file} \t " \
  "read Polymath solution from {json-file} and insert into VC template\n" \
// clang-format on

/// Read command line options related to Polymath RL training. Includes
/// converting a Polymath solution synthesis constraint to an RL scorer VC
/// template, and inserting a solution into an RL scorer VC template.
///
/// \param cmdlinet: Command line input
/// \param options: command Parsed options
void parse_polymath_training_options(
  const class cmdlinet &cmdline,
  class optionst &options);

/// Applies transformations used during Polymath RL training.
///
/// \param goto_model: Polymath solution synthesis constraint to be converted to
/// an RL scorer VC template, or an RL scorer VC template into which to insert a
/// solution.
/// \param options: command line options
void polymath_training(class goto_modelt &goto_model, const optionst &options);
