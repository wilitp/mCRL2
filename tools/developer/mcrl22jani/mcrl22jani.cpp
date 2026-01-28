// Author(s): Jan Friso Groote
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl22lps.cpp
/// \brief This tool linearises mcrl2 specifications into linear
///         form.

#include "mcrl2/atermpp/aterm.h"
#include "mcrl2/data/enumerator.h"
#include "mcrl2/data/fourier_motzkin.h"
#include "mcrl2/data/real_utilities.h"
#include "mcrl2/data/rewriter_tool.h"
#include <boost/json/src.hpp>
#include "mcrl2/data/substitutions/maintain_variables_in_rhs.h"
#include "mcrl2/lps/io.h"
#include "mcrl2/lps/linearise.h"
#include "mcrl2/utilities/input_output_tool.h"
#include <mcrl2/data/data_expression.h>
#include <mcrl2/lps/stochastic_specification.h>
#include <mcrl2/process/process_equation.h>
#include <mcrl2/process/process_identifier.h>
#include <regex>
#include <variant>

// linear process libraries.
#include "mcrl2/lps/constelm.h"
#include "mcrl2/lps/linearise.h"
#include "mcrl2/lps/linearise_allow_block.h"
#include "mcrl2/lps/linearise_communication.h"
#include "mcrl2/lps/linearise_rename.h"
#include "mcrl2/lps/linearise_utility.h"
#include "mcrl2/lps/replace_capture_avoiding_with_an_identifier_generator.h"
#include "mcrl2/lps/sumelm.h"

#include "mcrl2/lps/detail/ultimate_delay.h"

// Process libraries.
#include "mcrl2/process/alphabet_reduce.h"
#include "mcrl2/process/balance_nesting_depth.h"
#include "mcrl2/process/process_expression.h"

using mcrl2::data::tools::rewriter_tool;
using mcrl2::utilities::tools::input_output_tool;

// For Aterm library extension functions
using namespace atermpp;
using namespace mcrl2;
using namespace mcrl2::core;
using namespace mcrl2::core::detail;
using namespace mcrl2::data;
using namespace mcrl2::data::detail;
using namespace mcrl2::lps;
using namespace mcrl2::process;


class jani_translation_error : public mcrl2::runtime_error
{
  public:
  jani_translation_error(const std::string& message)
    : mcrl2::runtime_error(message)
  {}
};

class pcrl_to_automaton_translator{

  private:
    process::process_specification spec;
    boost::json::object jani_automaton;
    const process_instance& initial_process_call;
    // keeps track of states in sequential compositions
    std::vector<boost::json::object> sequentialCompositionStack; 
    uint stateCounter = 0;
    boost::json::object deltaState;

    const std::string DELTA_STATE_NAME = "delta_state";
    std::map<process_instance, boost::json::object> processInstanceStateMap;


  boost::json::object newState() {
     boost::json::object state{
      {"name", "state_" + std::to_string(stateCounter)}
    };

    stateCounter++;

    return state;
  }

  
  void ensureDeltaState() {
    if (deltaState.empty()) {
      deltaState = boost::json::object{
        {"name", DELTA_STATE_NAME}
      };
      addStateToAutomaton(deltaState);
    }
  }

  void addStateToAutomaton(const boost::json::object& state) {
    jani_automaton["locations"].as_array().push_back(state);
  }

  void addEdgeToAutomaton(const boost::json::object& edge) {
    jani_automaton["edges"].as_array().push_back(edge);
  }

  boost::json::object stateForProcessInstance(const process_instance& instance) {

    // check if state already exists
    if (processInstanceStateMap.find(instance) != processInstanceStateMap.end()) {
      return processInstanceStateMap[instance];
    } else {

      boost::json::object state{
        {"name", "state_for_" + pp(instance.identifier())}
      };

      processInstanceStateMap[instance] = state;

      auto identifier = instance.identifier();

      // std::cout << "Processing process instance: " << pp(instance) << std::endl;

      // lookup for process expression
      auto expr = std::find_if(spec.equations().begin(), spec.equations().end(),
        [&identifier](const process_equation& eqn) {
          return eqn.identifier() == identifier;
        });
      
      addStateToAutomaton(state);
      
      
      // fail if equation not found
      if (expr == spec.equations().end()) {
        throw jani_translation_error("Process equation not found for identifier: " + process::pp(identifier));
      }

      auto expression = expr.base()->expression();


      translateProcessExpression(expression, state["name"].as_string().c_str());
      return state;
    }
  }

  // get state for righthand side of sequential composition
  // if it already exists, otherwise create a new one
  boost::json::object getStateForRighthandSide(const process_expression& expr) {
    // check if state already exists
    if(is_process_instance(expr)) {
      auto instance = down_cast<process_instance>(expr);
      instance.identifier();
    }
    return boost::json::object();
  }

  boost::json::object makeEdge(const std::string& source, const std::string& target, const std::string& action) {
    return boost::json::object{
      {"action", action},
      {"location", source},
      {"destinations", boost::json::array({boost::json::object({{"location", target}})})}
    };
  }

  boost::json::object makeSilentEdge(const std::string& source, const std::string& target) {
    return boost::json::object{
      {"location", source},
      {"destinations", boost::json::array({boost::json::object({{"location", target}})})}
    };
  }

  void translateProcessExpression(const process_expression& expr, std::string previousStateName) {

    if(is_action(expr)) {

      boost::json::object target;

      if (sequentialCompositionStack.empty()) {
        target = newState();
        addStateToAutomaton(target);
      } else {
        target = sequentialCompositionStack.back();
      }

      addEdgeToAutomaton(
        makeEdge(previousStateName, target["name"].as_string().c_str(), pp(down_cast<action>(expr).label()))
      );

    } else if(is_delta(expr)) {
      // TODO: check if we can avoid adding a tau transition to delta state here
      ensureDeltaState();
      addEdgeToAutomaton(
        makeSilentEdge(
         previousStateName,
         DELTA_STATE_NAME
        )
      );
    } else if(is_seq(expr)) {
      auto left = process::seq(expr).left();
      auto right = process::seq(expr).right();

      boost::json::object intermediateState = newState();
      addStateToAutomaton(intermediateState);

      // push intermediate state to stack
      sequentialCompositionStack.push_back(intermediateState);

      // translate left part
      translateProcessExpression(left, previousStateName);

      // pop intermediate state from stack
      sequentialCompositionStack.pop_back();

      // translate right part
      translateProcessExpression(right, intermediateState["name"].as_string().c_str());

    } else if(is_choice(expr)) {
      auto left = process::choice(expr).left();
      auto right = process::choice(expr).right();

      // translate left part
      translateProcessExpression(left, previousStateName);

      // translate right part
      translateProcessExpression(right, previousStateName);
    } else if(is_process_instance(expr)) {
      auto instance = down_cast<process_instance>(expr);
      // create edge to state for process instance
      boost::json::object targetState = stateForProcessInstance(instance);

      addEdgeToAutomaton(
        makeSilentEdge(previousStateName, targetState["name"].as_string().c_str())
      );
    } else {
      throw jani_translation_error("Unsupported process expression encountered during translation.");
    }
  }

  public:
    pcrl_to_automaton_translator(process::process_specification spec, const process_instance& initial_process_call)
    : initial_process_call(initial_process_call)
    {
      this->spec = spec;

      std::string name;

      name = pp(initial_process_call.identifier());

      jani_automaton = {
        {"name", name},
        {"locations", boost::json::array()},
        {"edges", boost::json::array()}
      };
    }


    boost::json::object translate(){

      auto initialState = newState();
      addStateToAutomaton(initialState);

      jani_automaton["initial-locations"] = boost::json::array({initialState["name"].as_string().c_str()});

      translateProcessExpression(initial_process_call, initialState["name"].as_string().c_str());

      return jani_automaton;
    };
};

using sync_vector = std::pair<std::vector<std::string>, std::multiset<std::string>>;
using inner_matrix = std::vector<sync_vector>;

class syncs_matrix {
  // vector of rows, in which each row has a left-hand side of ordered actions
  // and a right-hand side of a multiset of actions.
  inner_matrix matrix;

  private:

    syncs_matrix(const inner_matrix& m)
      : matrix(m)
    {}


  public:

  syncs_matrix(std::vector<std::string> actions) {
    for (const auto& action : actions) {
      matrix.push_back(
        std::make_pair(
          std::vector<std::string>{action},
          std::multiset<std::string>{action}
        )
      );
    }
  }

  syncs_matrix operator||(const syncs_matrix& other) {
    // Note: this mutates the current object
    // and also internal structures from operands. Take into account when debugging.
    inner_matrix newMatrix;

    // assumes invariant that all vectors in lhs have the same size
    // and that matrices are non-empty
    assert(this->matrix.size() > 0);
    assert(other.matrix.size() > 0);
    uint thisWidth = this->matrix[0].first.size();
    uint otherWidth = other.matrix[0].first.size();

    // explicitly add rows for independent multiactions for the composed processes
    for (const auto& thisRow : this->matrix) {
      assert(thisRow.first.size() == thisWidth);
      sync_vector newRow;
      newRow.first.insert(newRow.first.end(), thisRow.first.begin(), thisRow.first.end());
      newRow.first.insert(newRow.first.end(), otherWidth, "null"); // pad with empty actions
      newRow.second = thisRow.second;
      newMatrix.push_back(newRow);
    }
    for (const auto& otherRow : other.matrix) {
      assert(otherRow.first.size() == otherWidth);
      sync_vector newRow;
      newRow.first.insert(newRow.first.end(), otherRow.first.begin(), otherRow.first.end());
      newRow.first.insert(newRow.first.end(), thisWidth, "null"); // pad with empty actions
      newRow.second = otherRow.second;
      newMatrix.push_back(newRow);
    }
    
    // now add synchronized rows
    for (const auto& otherRow : other.matrix) {
      for (const auto& thisRow : this->matrix) {

        // concatenate left-hand sides
        std::vector<std::string> newLHS = thisRow.first;
        newLHS.insert(newLHS.end(), otherRow.first.begin(), otherRow.first.end());

        // add multisets on right-hand sides
        std::multiset<std::string> newRHS = thisRow.second;
        newRHS.insert(otherRow.second.begin(), otherRow.second.end());

        newMatrix.push_back(
          std::make_pair(
            newLHS,
            newRHS
          )
        );
      }
    }
    return syncs_matrix(newMatrix);
  }

  syncs_matrix hide(const std::set<std::string>& actionsToHide) {

    for(const auto& action : actionsToHide) {
      // delete action from all multiactions possible in order to make them invisible / internal
      // Note: when a multiset end up empty, this should signify a tau action.
      for (auto& row : matrix) {
        row.second.erase(action);
      }
    }
    return *this;
  }

  syncs_matrix rename(const std::map<std::string, std::string>& renamings) {
    for(auto& renaming : renamings) {
      const std::string& from = renaming.first;
      const std::string& to = renaming.second;

      for (auto& row : matrix) {
        // remove renamed label
        auto ocurrences = row.second.erase(from);

        // introduce new label to multiaction as many times as needed
        for (uint i = 0; i < ocurrences; i++) {
          row.second.insert(to);
        }
      }
    }
    return *this;
  }

  syncs_matrix comm(const std::set<std::pair<std::multiset<std::string>, std::string>>& comms) {

    for (auto& row : matrix) {

      bool isSubMultiset = std::all_of(
        comms.begin(),
        comms.end(),
        [&row](const auto& commPair) {
          const auto& commMultiset = commPair.first;
          for (const auto& action : commMultiset) {
            if (commMultiset.count(action) < row.second.count(action)) {
              return false;
            }
          }
          return true;
        }
      );
      
      if (!isSubMultiset) {
        continue;
      }

      // Note: it's ok to do this sequentially
      // as no action can occur in both sides of different communications

      for (const auto& commPair : comms) {
        const auto& commMultiset = commPair.first;
        const auto& commResult = commPair.second;

        // remove the communicating actions from the multiset
        for (const auto& action : commMultiset) {
          row.second.erase(row.second.find(action));
        }
        // add the resulting action to the multiset
        row.second.insert(commResult);
      }
    }
    
    return *this;
  }

  // NOTE: allow works on multiactions, block does not,
  // go figure.
  syncs_matrix allow(const std::set<std::multiset<std::string>>& multiactionsToAllow) {
    for (auto row = matrix.begin(); row != matrix.end(); row++) {
      if (multiactionsToAllow.contains(row->second)) {
        continue;
      } else {
        matrix.erase(row);
      }
    }
    return *this;
  }
  syncs_matrix block(const std::set<std::string>& actionsToBlock) {
    for (const auto& action : actionsToBlock) {
      // delete action from all multiactions possible in order to block them
      for (auto row = matrix.begin(); row != matrix.end(); row++) {
        if (row->second.contains(action))
          matrix.erase(row);
      }
    }
    return *this;
  }

};


class jani_translator
{
  private:
  // gets all process identifiers that are reachable from the initial process
  // for now assumed to be pcrl
  // TODO: determine how to rewrite a spec so that all parallel compositions are in the initial process
  std::set<process_instance> collectPcrlProcessesRec(const process_expression& expr) {
    if (is_process_instance(expr)) {
      return {down_cast<process_instance>(expr)};
    }
    else if (is_merge(expr)) {
        auto idsLeft = collectPcrlProcessesRec(process::merge(expr).left());
        auto idsRight = collectPcrlProcessesRec(process::merge(expr).right());
        idsLeft.insert(idsRight.begin(), idsRight.end());
        return idsLeft;
    }
    else {
      throw jani_translation_error("Unsupported process expression encountered during pCRL process collection.");
    }
  }
  std::set<process_instance> collectPcrlProcesses() {
    auto initialProcess = spec.init();

    return collectPcrlProcessesRec(initialProcess);
  }


  // translates prcl process equation to jani automaton
  boost::json::object translate_process_equation(const process_instance& procInst) {

    mCRL2log(mcrl2::log::info) << "Translating process equation for: " << process::pp(procInst) << std::endl;

    pcrl_to_automaton_translator translator(spec, procInst);
    auto automaton = translator.translate();
    return automaton;
  }

  void translateActions() {
    // for now, just add all action labels from the specification
    // TODO: add global transient variables for communicating actions
    for (const auto& actionLabel : spec.action_labels()) {
      jani_actions.push_back(
        boost::json::object{
          {"name", pp(actionLabel)}
        }
      );
    }
  }

public:
  boost::json::object jani_model;
  boost::json::array jani_actions;
  boost::json::array jani_variables;
  boost::json::array jani_automata;
  boost::json::array jani_edges;
  boost::json::array jani_system_elements;

  process::process_specification spec;

  // constructor
  jani_translator(const process::process_specification& specification)
    : spec(specification){}

  boost::json::object translate_process_specification()
  {

    translateActions();
    std::set<process_instance> prclProcesses = collectPcrlProcesses();

    for (const auto& procInst : prclProcesses) {
      // std::cout << "Found pCRL process: " << process::pp(procInst) << std::endl;

      jani_system_elements.push_back(
          boost::json::value({{"automaton", pp(procInst)}})
      );
      auto automaton = translate_process_equation(procInst);
      jani_automata.push_back(automaton);
    }


    return boost::json::object(
      {
        {"name", "mCRL2_to_JANI_model"},
        {"type", "pta"},
        {"jani-version", 1},
        {"variables", jani_variables},
        {"automata", jani_automata},
        {"actions", jani_actions},
        {"system", {
          {"elements", jani_system_elements}
          }
        }
      }
    );
  }

};

class mcrl22jani_tool : public rewriter_tool<input_output_tool>
{
  using super = rewriter_tool<input_output_tool>;

private:
  mcrl2::lps::t_lin_options m_linearisation_options;
  // bool noalpha;   // indicates whether alpha reduction is needed.
  bool opt_check_only = false;

  bool m_print_ast{false}; // indicates whether the abstract syntax tree should be printed

protected:

  void add_options(mcrl2::utilities::interface_description& desc) override
  {
    // no options for now
  }

  void parse_options(const mcrl2::utilities::command_line_parser& parser) override
  {
    // no options for now
  }

public:

  mcrl22jani_tool()
    : super("mcrl22jani",
        "Guillermo de Ipola",
        "translate an mCRL2 specification to JANI format",
        "Translate the mCRL2 specification from stdin and writes the resulting JANI model to stdout."
      )
  {}

  bool run() override
  {

    mcrl2::process::process_specification spec;
    if (input_filename().empty())
    {
      // parse specification from stdin
      mCRL2log(mcrl2::log::verbose) << "Reading input from stdin..." << std::endl;
      spec = mcrl2::process::parse_process_specification(std::cin);
    }
    else
    {
      mCRL2log(mcrl2::log::verbose) << "Reading input from file '" << input_filename() << "'..." << std::endl;
      std::ifstream instream(input_filename().c_str(), std::ifstream::in | std::ifstream::binary);
      if (!instream.is_open())
      {
        throw mcrl2::runtime_error("Cannot open input file: " + input_filename() + ".");
      }
      spec = mcrl2::process::parse_process_specification(instream);
      instream.close();
    }

    // Report on well-formedness
    if (input_filename().empty())
    {
      mCRL2log(mcrl2::log::info) << "stdin contains a well-formed mCRL2 specification" << std::endl;
    }
    else
    {
      mCRL2log(mcrl2::log::info) << "the file '" << input_filename() << "' contains a well-formed mCRL2 specification"
                                 << std::endl;
    }

    mCRL2log(mcrl2::log::info) << mcrl2::process::pp(spec, false) << std::endl;

    // check that spec is linearisable
    // mcrl2::lps::stochastic_specification linear_spec(mcrl2::lps::linearise(spec, m_linearisation_options));
    jani_translator translator(spec);


    // std::cout << "Translating to JANI..." << std::endl;

    auto janiModel = translator.translate_process_specification();

    std::cout << janiModel << std::endl;

    return true;
  }
};

int main(int argc, char** argv)
{
  return mcrl22jani_tool().execute(argc, argv);
}
