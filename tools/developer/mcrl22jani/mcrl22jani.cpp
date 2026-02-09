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


class scope {
  public:
    // maps variable names to their allocated local 
    // variable in the JANI automaton.
    std::map<std::string, std::string> table;
    bool isProcessScope = false;

    scope() = default;

    scope(bool isProcessScope) : isProcessScope(isProcessScope) {}
};

using jani_var_name = std::string;
using mcrl2_var_name = std::string;

using readingActionSet = std::set<std::string>;


boost::json::value convert_sort_expression(const data::sort_expression& sort)
{
  if (data::sort_bool::is_bool(sort))
  {
    return "bool";
  }
  else if (data::sort_int::is_int(sort))
  {
    return "int";
  }
  else if (data::sort_nat::is_nat(sort))
  {
    return boost::json::object{
      { "base", "int" },
      {"kind", "bounded"},
      {"lower-bound", 0}
    };
  }
  else if (data::sort_pos::is_pos(sort))
  {
    return boost::json::object{
      {"base", "int"},
      {"kind", "bounded"},
      {"lower-bound", 1}
    };
  }
  else
  {
    throw mcrl2::runtime_error("Jani only supports sorts bool, int, nat and pos. "
      "It does not support sort " + pp(sort) + ".");
  }
}

using incomplete_edge_assignments = std::vector<std::pair<boost::json::object*, std::vector<boost::json::value>>>;

using write_reads_map = std::map<std::string, std::vector<std::string>>;

class pcrl_to_automaton_translator{
private:

    incomplete_edge_assignments& incompleteEdgeAssignments;

    readingActionSet readingActions;

    std::string currentProcessName;

    boost::json::array localVariables;
    std::vector<scope> scopes;
    // if a variable is declared already, we need to append a number since
    // automaton variables don't have scopes.
    // Note: this is redundant, since variables in the table will have the numbers,
    // this just makes it faster to find the next available number.
    std::map<jani_var_name, uint> counters;
    // keeps track of whether a variable needs to be read
    std::set<jani_var_name> readSet;
public:

    bool requiresReading(const jani_var_name& var) const {
      return readSet.contains(var);
    }

    void unmarkForReading(const jani_var_name& var) {
      readSet.erase(var);
    }

    void markForReading(const jani_var_name& var) {
      readSet.insert(var);
    }

    void clearScopes() {
      auto it = scopes.begin();
      scopes.erase(it, scopes.end());
    }
    void registerVar(const variable& var, const std::string& processName, bool isParam = false) {
      scope& scope = scopes.back();
      std::string baseName;
      auto varName = static_cast<std::string>(var.name());
      if (isParam) {
        baseName = processName + "_param_" + varName;
      } else {
        baseName = processName + "_" + varName;
      }
      uint& counter = counters[baseName];
      jani_var_name jani_var = baseName;

      if (!isParam) {
        markForReading(jani_var);
      }
      if (counter > 0 && !isParam) {
        jani_var += "_" + std::to_string(counter);
      }

      if (counter == 0 || !isParam) {
        localVariables.push_back(boost::json::object{
          {"name", jani_var},
          {"type", convert_sort_expression(var.sort())}
        });
      }
      scope.table[varName] = jani_var;
      counter++;
    }
    void enterScope() {
      scopes.push_back(scope());
    }

    void enterProcessScope() {
      scopes.push_back(scope(true));
    }

    void leaveScope() {
      scopes.pop_back();
    }

    jani_var_name getVariable(mcrl2_var_name name) const {
      for(auto it = scopes.rbegin(); it != scopes.rend(); ++it) {
        auto scope = *it;
        if (scope.table.find(name) != scope.table.end()) {
          return scope.table[name];
        }
        if (scope.isProcessScope) {
          // don't look past the current process scope
          break;
        }
      }
      throw jani_translation_error("Variable not found in symbol table: " + name);
    }

  private:
    process::process_specification spec;
    boost::json::object jani_automaton;
    const process_instance& initial_process_call;
    // keeps track of states in sequential compositions
    std::vector<boost::json::object> sequentialCompositionStack; 
    uint stateCounter = 0;
    boost::json::object deltaState;

    const std::string DELTA_STATE_NAME = "delta_state";
    std::map<process_identifier, boost::json::object> processInstanceStateMap;


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

  process_equation& lookup_process_equation(const process_identifier& id) {
    auto it = std::find_if(spec.equations().begin(), spec.equations().end(),
            [&id](const process_equation& eqn) {
              return eqn.identifier() == id;
            });

      // fail if equation not found
      if (it == spec.equations().end()) {
        throw jani_translation_error("Process equation not found for identifier: " + process::pp(id));
      }
    
    return *it.base();

  }

  boost::json::object stateForProcessInstance(const process_instance& instance) {


    auto identifier = instance.identifier();

    currentProcessName = pp(identifier);

    // lookup for process expression
    auto eq = lookup_process_equation(identifier);

    for (auto& param : eq.formal_parameters()) {
      registerVar(param, pp(instance.identifier()), true);
    }

    // check if state already exists
    if (processInstanceStateMap.find(identifier) != processInstanceStateMap.end()) {
      return processInstanceStateMap[identifier];
    } else {

      boost::json::object state{
        {"name", "state_for_" + pp(instance.identifier())}
      };

      processInstanceStateMap[identifier] = state;

      addStateToAutomaton(state);

      auto expression = eq.expression();

      translateProcessExpression(expression, state["name"].as_string().c_str());
      return state;
    }
  }

  boost::json::object makeEdge(const std::string& source, const std::string& target, const std::string& action, const boost::json::array& assignments = boost::json::array({})) {
    return boost::json::object{
      {"action", action},
      {"location", source},
      {"destinations", boost::json::array({boost::json::object({{"location", target}})})},
      {"assignments", assignments}
    };
  }

  boost::json::object makeSilentEdge(const std::string& source, const std::string& target, const boost::json::array& assignments = boost::json::array({})) {
    return boost::json::object{
      {"location", source},
      {"destinations", boost::json::array({boost::json::object({{"location", target}})})},
      {"assignments", assignments}
    };
  }

  jani_var_name getJaniVarForParam(const std::string& param, const std::string& processName) {
    return processName + "_param_" + param;

  }

  boost::json::array compute_read_assignments(const action& act) {
    boost::json::array assignments;
    uint i = 0;
    auto actionName = pp(act.label());
    for (auto& arg : act.arguments()) {
      auto errorMsg = "The action " + actionName + " has been marked as a reading action and can only get quantified, unread variables as arguments."
          "the offending expression is " + pp(arg) + " of order " + std::to_string(i + 1) + ".";

      if(!is_variable(arg)) {
        throw jani_translation_error(
          errorMsg
        );
      } 

      
      auto var = down_cast<variable>(arg);

      jani_var_name jani_var = getVariable(pp(var.name()));
      if(!requiresReading(jani_var)) {
        throw jani_translation_error(errorMsg + " Variable was not marked for reading");
      }

      // assign from global transient variable [actionName][index or signature parameter]
      assignments.push_back(
        boost::json::object({
          {"ref", getVariable(var.name())},
          {"value", actionName + "_" + std::to_string(i)},
          {"index", 1}
        })
      );
      i++;
    }

    return assignments;
  }

  boost::json::array compute_process_assignments(const process_instance& instance) {
    data_expression_list arguments = instance.actual_parameters();
    auto eq = lookup_process_equation(instance.identifier());
    variable_list parameters = eq.formal_parameters();

    // calculate jani names to assign
    std::vector<jani_var_name> lhss;
    for (auto& param : parameters) {
      lhss.push_back(getJaniVarForParam(static_cast<std::string>(param.name()).c_str(), pp(instance.identifier())));
    }

    // calculate jani expressions to assign
    std::vector<boost::json::value> rhss;
    for (auto& arg : arguments) {
      rhss.push_back(convert_data_expression(arg));
    }

    assert(lhss.size() == rhss.size());

    // merge them into the assignments array
    boost::json::array assignments;

    for (uint i=0; i < lhss.size(); i++){
      assignments.push_back(
        boost::json::object {
          {"ref", lhss[i]},
          {"value", rhss[i]}
        }
      );
    }

    return assignments;
  }


  boost::json::value convert_data_expression(const data::data_expression& e_in, bool varsForReadingAllowed = false, bool topLevel = true)
  {
    rewriter r;
    const data::data_expression e = r(e_in);
    if (is_variable(e))
    {
      // check the variable doesn't need reading
      // auto varName = static_cast<std::string>(atermpp::down_cast<data::variable>(e).name()).c_str();
      auto varName = pp(atermpp::down_cast<data::variable>(e).name());
      auto janiVar = getVariable(varName);
      if(requiresReading(janiVar) && (!topLevel || !varsForReadingAllowed)) {
        throw jani_translation_error("This variable requires reading, can't be used in an expression before it's used in an action receiving a value.");
      }
      return boost::json::value(janiVar);
    }
    else if (data::sort_pos::is_positive_constant(e) ||
      data::sort_nat::is_natural_constant(e) ||
      data::sort_int::is_integer_constant(e)) {
      return std::stoi(pp(e));
    }
    else if (data::sort_bool::is_true_function_symbol(e)) {
      return true;
    }
    else if (data::sort_bool::is_false_function_symbol(e)) {
      return false;
    }
    else if (data::sort_bool::is_not_application(e))
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"op", reinterpret_cast<const char*>(u8"¬")},
        {"exp", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (is_greater_application(e)) // > is not supported within jani, and thus should be flipped
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"left", convert_data_expression(appl[1], topLevel=false)},
        {"op", "<"},
        {"right", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (is_greater_equal_application(e)) // >= is not supported within jani, and thus should be flipped
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"left", convert_data_expression(appl[1], topLevel=false)},
        {"op", reinterpret_cast<const char*>(u8"≤")},
        {"right", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (data::sort_bool::is_implies_application(e)) {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"op", "ite"},
        {"if", convert_data_expression(appl[0], topLevel=false)},
        {"then", convert_data_expression(appl[1], topLevel=false)},
        {"else", "true"}
      };
    }
    else if (data::sort_real::is_floor_application(e) ||
      data::sort_real::is_ceil_application(e))
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"op", pp(appl.head())},
        {"exp", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (data::is_application(e) && e.size() == 3) {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return boost::json::object{
        {"left", convert_data_expression(appl[0], topLevel=false)},
        {"op", convert_operator_to_jani(appl.head())},
        {"right", convert_data_expression(appl[1], topLevel=false)}
      };
    }
    else
    {
      throw mcrl2::runtime_error("Jani only supports expressions true, false and numbers. "
        "It does not support the main operator in the expression " + pp(e) + ".");
    }
  }


  std::string convert_operator_to_jani(const data::data_expression& opid) const {
    if (std::string op = mcrl2::data::pp(opid);
      "!=" == op) 
    {
      return reinterpret_cast<const char*>(u8"≠");
    }
    else if ("==" == op) 
    {
      return "=";
    }
    else if ("<=" == op) 
    {
      return reinterpret_cast<const char*>(u8"≤");
    }
    else if ("&&" == op) 
    {
      return reinterpret_cast<const char*>(u8"∧");
    }
    else if ("||" == op) 
    {
      return reinterpret_cast<const char*>(u8"∨");
    }
    else if ("@cReal" == op) 
    { 
      return "/"; // threat real numbers as a division operator
    }
    else 
    {
      return op.c_str();
    }
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

      bool actionReads = false;

      auto act = down_cast<action>(expr);
      std::string actionName = pp(down_cast<action>(expr).label());
      std::vector<jani_var_name> varsToUnmark;
      for (const auto& arg : act.arguments()) {
        for (const auto& var : data::find_free_variables(arg)) {
          auto varName = static_cast<std::string>(var.name());
          auto janiVar = getVariable(varName);
          if (requiresReading(janiVar)) {
            actionReads = true; 
            varsToUnmark.push_back(janiVar);
            readingActions.insert(actionName);
          }
        }
      }

      // TODO:
      // - compute assignments related to READING if applicable
      boost::json::array assignments({});
      if (actionReads) {
        assignments = compute_read_assignments(act);
      }


      for (auto& janiVar : varsToUnmark) {
        unmarkForReading(janiVar);
      }

      // TODO:
      // - somehow compute assignments realted to writing, probably need to compute the syncs before translating automata
      auto edge = makeEdge(previousStateName, target["name"].as_string().c_str(), actionName, assignments);

      if (!actionReads) {
        // this is a writing action, so track it's edge and assignments

        std::vector<boost::json::value> janiArgs;

        for (auto& arg : act.arguments()) {
          janiArgs.push_back(convert_data_expression(arg));
        }

        incompleteEdgeAssignments.push_back(std::make_pair(&edge,janiArgs));
      }


      addEdgeToAutomaton(edge);

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

      auto assignments = compute_process_assignments(instance);

      enterScope();
      boost::json::object targetState = stateForProcessInstance(instance);


      addEdgeToAutomaton(
        makeSilentEdge(previousStateName, targetState["name"].as_string().c_str(), assignments=assignments)
      );
      leaveScope();
    } else if(is_sum(expr)) {
      auto summation = down_cast<sum>(expr);

      enterScope();
      for (const auto& var : summation.variables()) {
        registerVar(var, currentProcessName);
      }

      translateProcessExpression(summation.operand(), previousStateName);
      leaveScope();
    }  else {
      throw jani_translation_error("Unsupported process expression encountered during translation.");
    }
  }

  public:
    pcrl_to_automaton_translator(process::process_specification spec, const process_instance& initial_process_call, std::string automatonName, incomplete_edge_assignments incompleteEdgeAssignments)
    : initial_process_call(initial_process_call), incompleteEdgeAssignments(incompleteEdgeAssignments)
    {
      this->spec = spec;


      readingActions = readingActionSet({});

      jani_automaton = {
        {"name", automatonName},
        {"locations", boost::json::array()},
        {"edges", boost::json::array()}
      };
    }

    readingActionSet getReadingActions() const {
      return readingActions;
    }

    boost::json::object translate(){

      auto initialState = newState();
      addStateToAutomaton(initialState);

      jani_automaton["initial-locations"] = boost::json::array({initialState["name"].as_string().c_str()});

      translateProcessExpression(initial_process_call, initialState["name"].as_string().c_str());

      jani_automaton["variables"] = localVariables;

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

  std::string pp_action_vector(std::vector<std::string> actions) {
    std::string s="[";
    bool first=true;
    for (const auto& act : actions)
    {
      s=s+ (first?"":", ") + act;
      first=false;
    }
    s=s+ "]";
    return s;
  }


  // checks that all sync vectors include
  // exactly one writing action.
  // 0 would result in reading actions getting just the initial value
  // more than one would result in writing multiple values to the same channel
  void checkSyncs(readingActionSet readingActions) {
    for (auto& row : matrix) {
      
      uint writingActionCount = 0;
      uint readingActionCount = 0;

      for (auto& act : row.first) {
        if (act == "null") {
          continue;
        }
        if (readingActions.contains(act)) {
          readingActionCount += 1;
        } else {
          writingActionCount += 1;

        }
      }

      if (readingActionCount > 0 && writingActionCount != 1) {
        throw jani_translation_error(
          "Synchronization " + pp_action_vector(row.first) + " | " + formatResult(row.second) + " "
          "is illegal as there are reading actions involved but also more than one writing action."

        );
      }

      if (row.second.size() > 1) {
        throw jani_translation_error(
          "Synchronization " + pp_action_vector(row.first) + " | " + formatResult(row.second) + " "
          "is illegal, all multiactions should be part of a communication. If this multiactions does not serve any "
          "function to your model, please disallow it."
        );
      }
    }
    
  }

  std::string formatResult(std::multiset<std::string> multiAction) {
    std::string serializedMultiAction;
    
    if (multiAction.empty()) {
      return nullptr;
    } 

    serializedMultiAction = "";
    bool first = true;
    for (const auto& action : multiAction) {
      if (!first) {
        serializedMultiAction += "|";
      }
      serializedMultiAction += action;
      first = false;
    }

    return serializedMultiAction;

  }

  boost::json::value getResult(std::multiset<std::string> multiAction, std::set<std::string>& jani_multiactions_set) {
    std::string serializedMultiAction = formatResult(multiAction);
    
    if (multiAction.size() > 1) {
      jani_multiactions_set.insert(serializedMultiAction);
    }

    return boost::json::value(serializedMultiAction);
  }

  boost::json::array getSynchronisation(std::vector<std::string> actions) {
    boost::json::array synch;

    for (const auto& action : actions) {
      if (action == "null") {
        synch.push_back(boost::json::value(nullptr));
      } else {
        synch.push_back(boost::json::value(action));
      }
    }

    return synch;
  }

  boost::json::array toJsonArray(std::set<std::string>& jani_multiactions_set) {
      boost::json::array jsonArray;

      for (const auto& row : matrix) {
        jsonArray.push_back(
          boost::json::object{
            {"synchronise", getSynchronisation(row.first)},
            {"result", getResult(row.second, jani_multiactions_set)}
          }
        );
      }

      return jsonArray;
    }
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
      newRow.first.insert(newRow.first.end(), thisWidth, "null"); // pad with empty actions
      newRow.first.insert(newRow.first.end(), otherRow.first.begin(), otherRow.first.end());
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

      // Note: it's ok to do this sequentially
      // as no action can occur in both sides of different communications
      // actually no action can ocurr on the left side of more than one communication

      for (const auto& commPair : comms) {
        const auto& commMultiset = commPair.first;
        const auto& commResult = commPair.second;
        bool isSubMultiset = true;
        for (const auto& action : commMultiset) {
          if (commMultiset.count(action) > row.second.count(action)) {
            isSubMultiset = false;
          }
        }

        if (!isSubMultiset) {
          continue;
        }

        // remove the communicating actions from the multiset
        for (const auto& action : commMultiset) {
          auto it = row.second.find(action);
          assert(it != row.second.end());
          row.second.erase(it);
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
    for (auto row = matrix.begin(); row != matrix.end(); ) {
      if (multiactionsToAllow.contains(row->second)) {
        ++row;
      } else {
        row = matrix.erase(row);
      }
    }
    return *this;
  }
  syncs_matrix block(const std::set<std::string>& actionsToBlock) {
    for (const auto& action : actionsToBlock) {
      // delete every multiaction that contains a blocked action
      for (auto row = matrix.begin(); row != matrix.end();) {
        if (row->second.contains(action)) {
          row = matrix.erase(row);
        } else {
          ++row;
        }
      }
    }
    return *this;
  }

};


class jani_translator
{
  private:
  incomplete_edge_assignments incompleteEdgeAssignments;
  readingActionSet readingActions;
  std::map<process_identifier, uint> automatonCounters;
  // gets all process identifiers that are reachable from the initial process
  // for now assumed to be pcrl
  std::set<process_instance> collectPcrlProcessesRec(const process_expression& expr) {
    if (is_process_instance(expr)) {
      return {down_cast<process_instance>(expr)};
    }
    else if (is_merge(expr)) {
        auto idsLeft = collectPcrlProcessesRec(process::merge(expr).left());
        auto idsRight = collectPcrlProcessesRec(process::merge(expr).right());
        idsLeft.insert(idsRight.begin(), idsRight.end());
        return idsLeft;
    } else if(is_allow(expr)) {
        return collectPcrlProcessesRec(process::allow(expr).operand()) ;
    } else if(is_block(expr)) {
        return collectPcrlProcessesRec(process::block(expr).operand()) ;
    } else if(is_rename(expr)) {
        return collectPcrlProcessesRec(process::rename(expr).operand()) ;
    } else if(is_hide(expr)) {
        return collectPcrlProcessesRec(process::hide(expr).operand()) ;
    } else if(is_comm(expr)) {
        return collectPcrlProcessesRec(process::comm(expr).operand()) ;
    }
    else {
      mCRL2log(mcrl2::log::info) << "Unsupported process expression: " << process::pp(expr) << std::endl;
      throw jani_translation_error("Unsupported process expression encountered during pCRL process collection.");
    }
  }
  std::set<process_instance> collectPcrlProcesses() {
    auto initialProcess = spec.init();

    return collectPcrlProcessesRec(initialProcess);
  }

  syncs_matrix buildSyncsMatrixRec(const process_expression& expr) {
    if (is_process_instance(expr)) {
      // base case: single process instance
      std::vector<std::string> actionsVector;
      for (const auto& el : jani_actions) {
        actionsVector.push_back(el.as_object().at("name").as_string().c_str());
      }
      return syncs_matrix(actionsVector);
    }
    else if (is_merge(expr)) {
        auto leftMatrix = buildSyncsMatrixRec(process::merge(expr).left());
        auto rightMatrix = buildSyncsMatrixRec(process::merge(expr).right());
        return leftMatrix || rightMatrix;
    }
    else if (is_allow(expr)) {
        auto allowedActions = process::allow(expr).allow_set();
        std::set<std::multiset<std::string>> actionsToAllow;
        for (const auto& multiAction : allowedActions) {
          std::multiset<std::string> multiActionToInsert;
          for (const auto& action : multiAction.names()) {
            mCRL2log(mcrl2::log::info) << "Allowing action in syncs matrix: " << pp(action) << std::endl;
            multiActionToInsert.insert(pp(action));

          }
          actionsToAllow.insert(multiActionToInsert);
        }
        auto subMatrix = buildSyncsMatrixRec(process::allow(expr).operand());
        return subMatrix.allow(actionsToAllow);
    } else if (is_block(expr)) {
      auto blockedActions = process::block(expr).block_set();
      std::set<std::string> actionsToBlock;
      for (const auto& action : blockedActions) {
        mCRL2log(mcrl2::log::info) << "Blocking action in syncs matrix: " << pp(action) << std::endl;
        actionsToBlock.insert(pp(action));
      }
      auto subMatrix = buildSyncsMatrixRec(process::block(expr).operand());
      return subMatrix.block(actionsToBlock);
    } else if (is_hide(expr)) {
      auto hiddenActions = process::hide(expr).hide_set();
      std::set<std::string> actionsToHide;
      for (const auto& action : hiddenActions) {
        mCRL2log(mcrl2::log::info) << "Hiding action in syncs matrix: " << pp(action) << std::endl;
        actionsToHide.insert(pp(action));
      }
      auto subMatrix = buildSyncsMatrixRec(process::hide(expr).operand());
      return subMatrix.hide(actionsToHide);
    } else if (is_rename(expr)) {
      auto renamingList = process::rename(expr).rename_set();
      std::map<std::string, std::string> renamings;
      for (const auto& renaming : renamingList) {
        mCRL2log(mcrl2::log::info) << "Renaming action in syncs matrix: " << pp(renaming.source()) << " to " << pp(renaming.target()) << std::endl;
        renamings[pp(renaming.source())] = pp(renaming.target());
      }
      auto subMatrix = buildSyncsMatrixRec(process::rename(expr).operand());
      return subMatrix.rename(renamings);
    } else if (is_comm(expr)) {
      auto commSet = process::comm(expr).comm_set();
      std::set<std::pair<std::multiset<std::string>, std::string>> actionsToComm;
      for (const auto& commExp : commSet) {
        std::multiset<std::string> commLHS;
        for (const auto& action : commExp.action_name().names()) {
          commLHS.insert(pp(action));
        }
        actionsToComm.insert(std::make_pair(commLHS, pp(commExp.name())));
      }
      auto subMatrix = buildSyncsMatrixRec(process::comm(expr).operand());
      return subMatrix.comm(actionsToComm);
    }
    else {
      throw jani_translation_error("Unsupported process expression encountered during syncs matrix construction.");
    }
  }


  syncs_matrix buildSyncsMatrix() {
    auto initialProcess = spec.init();

    return buildSyncsMatrixRec(initialProcess);
  }


  // translates prcl process equation to jani automaton
  boost::json::object translate_process_equation(const process_instance& procInst) {

    mCRL2log(mcrl2::log::info) << "Translating process equation for: " << process::pp(procInst) << std::endl;

    std::string automatonName;
    if (automatonCounters.find(procInst.identifier()) == automatonCounters.end()) {
      automatonCounters[procInst.identifier()] = 0;
      automatonName = pp(procInst.identifier());
    } else {
      automatonName = pp(procInst.identifier()) + std::to_string(automatonCounters[procInst.identifier()]);
      automatonCounters[procInst.identifier()]++;
    }

    pcrl_to_automaton_translator translator(spec, procInst, automatonName, incompleteEdgeAssignments);
    auto automaton = translator.translate();
    auto automatonReadingActions = translator.getReadingActions();
    readingActions.insert(automatonReadingActions.begin(), automatonReadingActions.end());
    return automaton;
  }

  boost::json::value initial_value_for_sort(sort_expression sort) {
    if (data::sort_bool::is_bool(sort))
    {
      return false;
    }
    else if (data::sort_int::is_int(sort))
    {
      return 0;
    }
    else if (data::sort_nat::is_nat(sort))
    {
      return 0;
    }
    else if (data::sort_pos::is_pos(sort))
    {
      return 0;
    }
    else
    {
      throw jani_translation_error("Jani only supports sorts bool, int, nat and pos. "
        "It does not support sort " + pp(sort) + ".");
    }
  }

  void addTransientVars() {
    // for now, just add all action labels from the specification
    for (const auto& actionLabel : spec.action_labels()) {

      auto actionName = pp(actionLabel.name());

      // allocate transient variables for this actions inputs
      if (readingActions.contains(actionName)) {
        uint i = 0;
        for(const auto& sort : actionLabel.sorts() ) {
          auto jani_type = convert_sort_expression(sort);
          auto initial_value = initial_value_for_sort(sort);


          jani_variables.push_back(boost::json::object(
            {
              {"name", actionName + "_" + std::to_string(i)},
              {"initial-value", initial_value},
              {"type", jani_type}
            }
          ));
          i++;
        }

      }
    }
  }
  void translateActions() {
    // for now, just add all action labels from the specification
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
  std::set<std::string> jani_multiactions_set;
  boost::json::array jani_variables;
  boost::json::array jani_automata;
  boost::json::array jani_edges;
  boost::json::array jani_system_elements;

  process::process_specification spec;

  // constructor
  jani_translator(const process::process_specification& specification)
    : spec(specification) {
      readingActions = readingActionSet();
    }

  

  boost::json::object translate_process_specification()
  {

    std::set<process_instance> prclProcesses = collectPcrlProcesses();
    translateActions();
    auto syncsMatrix = buildSyncsMatrix();

    for (const auto& procInst : prclProcesses) {
      // std::cout << "Found pCRL process: " << process::pp(procInst) << std::endl;

      jani_system_elements.push_back(
          boost::json::value({{"automaton", pp(procInst.identifier())}})
      );
      auto automaton = translate_process_equation(procInst);
      jani_automata.push_back(automaton);
    }

    syncsMatrix.checkSyncs(readingActions);


    auto jsonMatrix = syncsMatrix.toJsonArray(jani_multiactions_set);

    // multiactions must be explicitly made a communication
    // "accidental multiactions are not allowed"
    // TODO: throw a proper error instead of asserting
    // assert(jani_multiactions_set.size() == 0);
    // for (auto& multiaction : jani_multiactions_set) {
    //   jani_actions.push_back(
    //     boost::json::object{
    //       {"name", multiaction}
    //     }
    //   );
    // }

    addTransientVars();

    addRandomThingToEdges();

    return boost::json::object(
      {
        {"name", "mCRL2_to_JANI_model"},
        {"type", "pta"},
        {"jani-version", 1},
        {"variables", jani_variables},
        {"automata", jani_automata},
        {"actions", jani_actions},
        {"system", {
          {"elements", jani_system_elements},
          {"syncs", jsonMatrix}
          }
        }
      }
    );
  }

  void addRandomThingToEdges() {
    for (auto& incompleteEdge : incompleteEdgeAssignments) {
      auto edge = *(incompleteEdge.first);
      edge["lalala"] = "hola";

    }
  }


  /*
  when processing a reading action, include its edge in a data structure that includes:
  - a reference to the edge
  - the (JANI) expressions it needs to assign
  
  later on, when we know which actions are reads, and which ones are writes, map every writing action
  to the set of reading actions that possible read it's inputs according to the syncs matrix.

  having this two data structures read (the edge tracking one, and the write -> reads map), we can
  add the remaining assignments to the edges for the writing actions.
  */


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
