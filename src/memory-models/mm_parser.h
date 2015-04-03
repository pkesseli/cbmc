/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MM_PARSER_H
#define CPROVER_MM_PARSER_H

#include <util/parser.h>
#include <util/std_code.h>

int yymmparse();

class mm_parsert:public parsert
{
public:
  codet parse_tree;

  virtual bool parse()
  {
    return yymmparse()!=0;
  }

  virtual void clear()
  {
    parse_tree.clear();
  }
};

extern mm_parsert mm_parser;

#endif
