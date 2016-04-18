#include <goto-programs/goto_functions.h>

#include <cegis/jsa/instrument/jsa_meta_data.h>

#define JSA_HEAP_TAG "tag-__CPROVER_jsa_abstract_heap"

bool is_jsa_heap(const typet &type)
{
  const irep_idt &type_id=type.id();
  if (ID_symbol == type_id)
    return id2string(to_symbol_type(type).get_identifier()) == JSA_HEAP_TAG;
  if (ID_struct != type_id) return false;
  const irep_idt tag(to_struct_type(type).get_tag());
  return id2string(tag) == JSA_HEAP_TAG;
}

#define JSA_ITERATOR_PREFIX JSA_PREFIX "iterator_"
#define JSA_LIST_PREFIX JSA_PREFIX "list_"

namespace
{
bool contains(const irep_idt &haystack, const std::string &needle)
{
  return std::string::npos != id2string(haystack).find(needle);
}
}

bool is_jsa_iterator(const irep_idt &id)
{
  return contains(id, JSA_ITERATOR_PREFIX);
}

bool is_jsa_list(const irep_idt &id)
{
  return contains(id, JSA_LIST_PREFIX);
}

source_locationt jsa_builtin_source_location()
{
  source_locationt loc;
  loc.set_file(JSA_MODULE);
  loc.set_function(goto_functionst::entry_point());
  return loc;
}