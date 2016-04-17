/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_COUNTEREXAMPLE_H_
#define CEGIS_JSA_COUNTEREXAMPLE_H_

#include <deque>
#include <map>

/**
 * @brief
 *
 * @details List of values per program location.
 */
typedef std::map<unsigned, exprt> jsa_counterexamplet;

typedef std::deque<jsa_counterexamplet> jsa_counterexamplest;

#endif /* CEGIS_JSA_COUNTEREXAMPLE_H_ */
