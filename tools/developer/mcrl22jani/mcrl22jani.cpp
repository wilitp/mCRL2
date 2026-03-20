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

#include <limits>
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
using namespace std;
using namespace boost;


// TODO: catch the (invalid) case where an automaton uses an action for writing and a latter one uses it for reading.
//   - reading and writing actions should be both tracked explicitely, so we can check at every turn that an action is not being used
//     in a different fashion than before.


class jani_translation_error : public mcrl2::runtime_error
{
  public:
  jani_translation_error(const string& message)
    : mcrl2::runtime_error(message)
  {}
};

json::value initial_value_for_sort(sort_expression sort) {
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
  else if (data::sort_real::is_real(sort))
  {
    return 0;
  }
  else
  {
    throw jani_translation_error("Jani only supports sorts bool, int, nat and pos. "
      "It does not support sort " + pp(sort) + ".");
  }
}

class scope {
  public:
    // maps variable names to their allocated local 
    // variable in the JANI automaton.
    map<string, string> table;
    bool isProcessScope = false;

    scope() = default;

    scope(bool isProcessScope) : isProcessScope(isProcessScope) {}
};

using jani_var_name = string;
using mcrl2_var_name = string;

using readingActionSet = set<string>;


json::value convert_sort_expression(const data::sort_expression& sort)
{
  if (data::sort_bool::is_bool(sort))
  {
    return "bool";
  }
  else if (data::sort_int::is_int(sort))
  {
    return "int";
  }
  else if (data::sort_real::is_real(sort))
  {
    return "real";
  }
  else if (data::sort_nat::is_nat(sort))
  {
    return json::object{
      { "base", "int" },
      {"kind", "bounded"},
      {"lower-bound", 0}
    };
  }
  else if (data::sort_pos::is_pos(sort))
  {
    return json::object{
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

using incomplete_edge_assignments = vector<pair<json::object*, vector<json::value>>>;

using write_reads_map = map<string, vector<string>>;

// assignment to be made on a transition leading to the initial state of a partial_automaton
// this is a map and not a list because unguarded recursion is not allowed, so we won't have to worry
// about multiple assignments to the same variable
using pending_assignments = list<json::array>;

// tracks what states are considered initial and/or terminating in the
// automaton associated to an expression.


class pcrl_to_automaton_translator{
private:

    incomplete_edge_assignments& incompleteEdgeAssignments;

    readingActionSet readingActions;

    string currentProcessName;

    json::array localVariables;
    vector<scope> scopes;
    // if a variable is declared already, we need to append a number since
    // automaton variables don't have scopes.
    // Note: this is redundant, since variables in the table will have the numbers,
    // this just makes it faster to find the next available number.
    map<jani_var_name, uint> counters;
    // keeps track of whether a variable needs to be read
    set<jani_var_name> readSet;
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
    jani_var_name registerVar(const variable& var, const string& processName, bool isParam = false) {
      scope& scope = scopes.back();
      string baseName;
      auto varName = static_cast<string>(var.name());
      if (isParam) {
        baseName = processName + "_param_" + varName;
      } else {
        baseName = varName;
      }
      uint& counter = counters[baseName];
      jani_var_name jani_var = baseName;

      if (counter > 0 && !isParam) {
        jani_var += "_" + to_string(counter);
      }

      if (!isParam) {
        markForReading(jani_var);
      }

      if (!isParam || (isParam && counter == 0)) {
        localVariables.push_back(json::object{
          {"name", jani_var},
          {"initial-value",  initial_value_for_sort(var.sort())},
          {"type", convert_sort_expression(var.sort())}
        });
      } 
      scope.table[varName] = jani_var;
      counter++;
      return jani_var;
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
    json::object jani_automaton;
    const process_instance& initial_process_call;
    // keeps track of states in sequential compositions
    vector<json::object> sequentialCompositionStack; 
    uint stateCounter = 0;
    json::object deltaState;

    const string DELTA_LOCATION_NAME = "delta_state";
    const string TERMINATION_LOCATION_NAME = "termination";
    map<string, string> processInstanceStateMap;
    map<string, string> stateProcessInstanceMap;


  json::object newState() {
    // TODO: add the state here and just return the name
    json::object state{
      {"name", "state_" + to_string(stateCounter)}
    };

    stateCounter++;

    return state;
  }

  
  void ensureDeltaState() {
    if (deltaState.empty()) {
      deltaState = json::object{
        {"name", DELTA_LOCATION_NAME}
      };
      addStateToAutomaton(deltaState);
    }
  }

  void addStateToAutomaton(const json::object& state) {
    jani_automaton["locations"].as_array().push_back(state);
  }

  void addEdgeToAutomaton(const json::object& edge) {
    string source = edge.at("location").as_string().c_str();
    string target = edge.at("destinations").at(0).at("location").as_string().c_str();
    jani_automaton["edges"].as_array().push_back(edge);
  }

  process_equation& lookup_process_equation(const process_identifier& id) {
    auto it = find_if(spec.equations().begin(), spec.equations().end(),
            [&id](const process_equation& eqn) {
              return eqn.identifier() == id;
            });

      // fail if equation not found
      if (it == spec.equations().end()) {
        throw jani_translation_error("Process equation not found for identifier: " + process::pp(id));
      }
    
    return *it.base();

  }


  json::object makeEdge(const string& source, const string& target, const string& action, const json::array& assignments = json::array({})) {
    return json::object{
      {"action", action},
      {"location", source},
      {"destinations", json::array({json::object({{"location", target}, {"assignments", assignments}})})},
    };
  }

  json::object makeSilentEdge(
    const string& source, const string& target, 
    const json::array& assignments = json::array({}),
    const json::object& guardExpression = json::object()
  ) {


    auto edge = json::object{
      {"location", source},
      {"destinations", json::array({json::object({{"location", target}, {"assignments", assignments}})})},
    };

    if (!guardExpression.empty()) {
      edge["guard"] = json::object({{"exp", guardExpression}});
    }

    return edge;
  }

  jani_var_name getJaniVarForParam(const string& param, const string& processName) {
    return processName + "_param_" + param;

  }

  json::array compute_read_assignments(const action& act) {
    json::array assignments;
    uint i = 0;
    auto actionName = pp(act.label());
    for (auto arg : act.arguments()) {
      auto errorMsg = "The action " + actionName + " has been marked as a reading action and can only get quantified, unread variables as arguments."
          " The offending expression is " + pp(arg) + ", argument number " + to_string(i + 1) + ".";


      // NOTE: this might not be necessary as in our communication scheme, types of summation variables need to be
      //       exactly the same as the ones specified in the action's declaration.
      while (is_application(arg)) {
        auto app = down_cast<application>(arg);
        auto opid = pp(app.head());

        
        // allow cast to real numbers, but not explicit division
        if(opid == "@cReal" && pp(app[1]) != "1") {
          throw jani_translation_error(errorMsg);
        } 

        // allow cast to either int or pos
        if (!(opid == "@cReal" || opid == "@cInt" || opid == "@cPos" || opid == "cNat")) {
          throw jani_translation_error(errorMsg);
        } 

        // just pprinting for debugging purposes
        vector<string> args;
        string func = pp(app.function());
        string head = pp(app.head());
        for (size_t i = 0; i < app.size(); i++) {
          args.push_back(pp(app[i]));
        }
        arg = (app)[0];
      }

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
        json::object({
          {"ref", getVariable(var.name())},
          {"value", actionName + "_" + to_string(i)},
          {"index", 1}
        })
      );
      i++;
    }

    return assignments;
  }

  json::value convert_data_expression(const data::data_expression& e_in, bool varsForReadingAllowed = false, bool topLevel = true)
  {
    rewriter r;
    const data::data_expression e = r(e_in);
    if (is_variable(e))
    {
      // check the variable doesn't need reading
      // auto varName = static_cast<string>(atermpp::down_cast<data::variable>(e).name()).c_str();
      auto varName = pp(atermpp::down_cast<data::variable>(e).name());
      auto janiVar = getVariable(varName);
      if(requiresReading(janiVar) && (!topLevel || !varsForReadingAllowed)) {
        throw jani_translation_error("This variable requires reading, can't be used in an expression before it's used in an action receiving a value.");
      }
      return json::value(janiVar);
    }
    else if (data::sort_pos::is_positive_constant(e) ||
      data::sort_nat::is_natural_constant(e) ||
      data::sort_int::is_integer_constant(e)) {
      return stoi(pp(e));
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
      return json::object{
        {"op", reinterpret_cast<const char*>(u8"¬")},
        {"exp", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (is_greater_application(e)) // > is not supported within jani, and thus should be flipped
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"left", convert_data_expression(appl[1], topLevel=false)},
        {"op", "<"},
        {"right", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (is_greater_equal_application(e)) // >= is not supported within jani, and thus should be flipped
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"left", convert_data_expression(appl[1], topLevel=false)},
        {"op", reinterpret_cast<const char*>(u8"≤")},
        {"right", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (data::sort_bool::is_implies_application(e)) {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
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
      return json::object{
        {"op", pp(appl.head())},
        {"exp", convert_data_expression(appl[0], topLevel=false)}
      };
    }
    else if (data::is_application(e) && e.size() == 3) {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
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


  string convert_operator_to_jani(const data::data_expression& opid) const {
    if (string op = mcrl2::data::pp(opid);
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

  void eraseStateByName(string removedStateName) {
    auto& states = jani_automaton["locations"].as_array();
    for (auto it = states.begin();it != states.end(); it++) {
      auto stateName = it->as_object()["name"].as_string().c_str();
      if (
        stateName == removedStateName
      ) 
      {
        states.erase(it);
        break;
      }
    }
  }


  // replaces `previousTarget` for `newTarget` in every edge where applicable
  void replaceEdgesTarget(string previousTarget, string newTarget) {
    auto& edges = jani_automaton["edges"].as_array();
    for (auto it = edges.begin(); it != edges.end(); it++) {
      auto& edge = it->as_object();
      auto target = edge["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
      if (target == previousTarget) {
        edge["destinations"].as_array()[0].as_object()["location"] = newTarget;
      }
    }
  }

  void ensureTermLocation() {
    // TODO: just save `found` in the class as `termLocationCreated`
    //       and skip the search
    bool found = false;
    for (auto& location : jani_automaton["locations"].as_array()) {
      if (location.as_object()["name"].as_string().c_str() == TERMINATION_LOCATION_NAME) {
        found = true;
      }
    }

    if (!found) {
      json::object terminationLocation{
        {"name", TERMINATION_LOCATION_NAME}
      };

      addStateToAutomaton(terminationLocation);
    }
  }

  // these keep track of the location associated to a subprocess expression and vice-versa
  using symbolic_process_expression = pair<process_expression, map<mcrl2_var_name, jani_var_name>>;
  map<symbolic_process_expression, string>subProcessStateMap;
  map<string, symbolic_process_expression> locationSubProcessMap;

  // used to set locations for sums, since their location is the location for its already
  // translated body
  void assignLocationForExpression(symbolic_process_expression expr, string locationName) {
      subProcessStateMap.insert({expr, locationName});
      locationSubProcessMap.insert({locationName, expr});
  }

  pair<string, bool> ensureLocationForExpression(symbolic_process_expression expr) {
    // user code must have followed the equations and call this function
    // only if it found the actual behavior

    if (subProcessStateMap.count(expr) == 0) {
      auto loc = newState();
      string name = loc["name"].as_string().c_str();
      addStateToAutomaton(loc);
      subProcessStateMap.insert({expr, name});
      locationSubProcessMap.insert({name, expr});
      return make_pair(name, true);
    } else {
      return make_pair(subProcessStateMap.at(expr), false);
    }
  }

  // Inserts pending assignments to an edge, after the existing assignments (if any).
  void insertPendingAssignmentsAfter(json::object& edge, pending_assignments pendingAssignments) {

    json::array newAssignments;

    // By default, we are inserting assignments starting on index 2
    int baseIndex = 2;

    bool edgeHasAssignments = edge.at("destinations").at(0).as_object().contains("assignments");

    // increase the base index one further than the maximum index in existing assignments
    if (edgeHasAssignments) {
      auto existingAssignments = edge.at("destinations").at(0).as_object().at("assignments").as_array();
      for (const auto& assignment : existingAssignments) {
        int currentIndex;
        if (assignment.as_object().contains("index")) {
          currentIndex = assignment.as_object().at("index").as_int64();
        } else {
          currentIndex = 0;
        }
        if (currentIndex >= baseIndex) {
          baseIndex = currentIndex + 1;
        }

        newAssignments.push_back(assignment);
      }
    }

    // add pending assignments with increasing index starting from baseIndex
    for (auto& atomicAssignmentSet : pendingAssignments) {
      for (auto& assignment : atomicAssignmentSet) {
        assignment.as_object()["index"] = baseIndex;
        newAssignments.push_back(assignment);
        baseIndex++;
      }
    }

    auto& destination =  edge.at("destinations").at(0).as_object();
    destination["assignments"] = newAssignments;
  }

  // Inserts pending assignments to an edge, before the existing assignments (if any).
  void insertPendingAssignmentsBefore(json::value& edge, pending_assignments pendingAssignments) {
    // By default, we are inserting assignments starting on index 2
    int baseIndex = -1;

    // decrease the base index one further than the minimum index in existing assignments
    if (edge.as_object().contains("assignments")) {
      auto existingAssignments = edge.as_object()["assignments"].as_array();
      for (const auto& assignment : existingAssignments) {
        int currentIndex = assignment.as_object().at("index").as_int64();
        if (currentIndex <= baseIndex) {
          baseIndex = currentIndex - 1;
        }
      }
    }
  }


  pair<string, pending_assignments> translateProcessExpression(const process_expression& expr) {

    auto fv = process::find_free_variables(expr);

    map<mcrl2_var_name, jani_var_name> varMap;

    for (const auto& var : fv) {
      varMap[var.name()] = getVariable(pp(var.name()));
    }

    symbolic_process_expression symExpr{expr, varMap};

    for (const auto& var : fv) {
      getVariable(pp(var.name()));
    }

    // just for debugging
    string exprs =  pp(expr);


    if(is_action(expr)) {

      // TODO:
      //   - check that quantified variables used in reading actions are *exactly* the same sort/type
      //     although that might seem overly restrictive, mCRL2 itself doesn't handle those type mismatches at all

      // Ensure a location exists for this action
      auto [locationName, created] = ensureLocationForExpression(symExpr);
      if (!created) {
        return {locationName, {}};
      }

      auto act = down_cast<action>(expr);
      string actionName = pp(act.label());

      // Ensure terminating location is in the graph
      ensureTermLocation();

      bool actionReads = false;
      vector<jani_var_name> varsToUnmark;
      for (const auto& arg : act.arguments()) {
        for (const auto& var : data::find_free_variables(arg)) {
          auto varName = static_cast<string>(var.name());
          auto janiVar = getVariable(varName);
          if (requiresReading(janiVar)) {
            actionReads = true; 
            varsToUnmark.push_back(janiVar);
            readingActions.insert(actionName);
          }
        }
      }

      json::array assignments({});
      if (actionReads) {
        assignments = compute_read_assignments(act);
      }


      for (auto& janiVar : varsToUnmark) {
        unmarkForReading(janiVar);
      }


      if (!actionReads) {
        // this is a writing action, so track its assignments
        // so as to assign to transient variables later

        uint i = 0;
        for (auto& arg : act.arguments()) {
          assignments.push_back(
            json::object({
              {"ref", to_string(i)},
              {"value", convert_data_expression(arg)}
            })
          );
          i++;
        }
      }


      // Ensure there's a transition from this location to the terminating location
      if (created) {
        auto edge = makeEdge(locationName, TERMINATION_LOCATION_NAME, actionName, assignments);

        addEdgeToAutomaton(edge);
      }

      return {locationName, {}};

    } else if(is_seq(expr)) {

      auto sequence = down_cast<seq>(expr);

      auto [locationName, created] = ensureLocationForExpression(symExpr); 

      if (!created) {
        return {locationName, {}};
      }

      auto p = sequence.left(); 
      auto q = sequence.right(); 

      // left part shouldn't have pending assignments, as we don't allow for process instances to occur
      auto [leftLocation, _] = translateProcessExpression(p);
      auto [rightLocation, pendingAssignments] = translateProcessExpression(q);


      // for every outgoing transition from the left part:
      //   if it's to the terminating location, copy it but aiming from this location to the right part's location
      //   if it's not, then copy it but aiming from this location to a new expression's we'll have to recurse on first.
      //   this expression is `[the expression corresponding to the aimed location] . [right part]`

      // TODO: handle pending assignments while copying edges.
      vector<json::object> newEdges;
      for (auto& edge : jani_automaton["edges"].as_array()) {
        auto& edgeObj = edge.as_object();
        auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
        auto source = edgeObj["location"].as_string().c_str();
        if (source == leftLocation) {
          json::object newEdge = edgeObj; // copy edge, we'll modify and add it back as a new edge
          newEdge["location"] = locationName;
          if (edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str() == TERMINATION_LOCATION_NAME) {
            newEdge["destinations"].as_array()[0].as_object()["location"] = rightLocation;
            insertPendingAssignmentsAfter(newEdge, pendingAssignments);
            newEdges.push_back(newEdge);
          } else {
            auto newExpr = seq(locationSubProcessMap.at(target).first, q);

            // new expression is a sequence, we know it won't have pending assignments
            auto [newLocation, _] = translateProcessExpression(newExpr);
            newEdge["destinations"].as_array()[0].as_object()["location"] = newLocation;
            newEdges.push_back(newEdge);
          }
        }
      }

      for (auto& newEdge : newEdges) {
        addEdgeToAutomaton(newEdge);
      }

      return {locationName, {}};
    } else if(is_choice(expr)) {

      // TODO:
      //   - include pending assignments for subexpressions in the negative indices of their first transitions
      //   - rewrite any guards in the first transitions according to this assignments

      // - Ensure a location exists for this choice
      auto [locationName, created] = ensureLocationForExpression(symExpr);
      if (!created) {
        return {locationName, {}};
      }
      auto choiceExpr = down_cast<choice>(expr);
      auto p = choiceExpr.left();
      auto q = choiceExpr.right();
      auto [leftLocation, leftPendingAssignments] = translateProcessExpression(p);
      auto [rightLocation, rightPendingAssignments] = translateProcessExpression(q);

      // - For each outgoing transition of the left side, copy it but going out of this location
      for (auto& edge : jani_automaton["edges"].as_array()) {
        auto& edgeObj = edge.as_object();
        auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
        auto source = edgeObj["location"].as_string().c_str();

        if (source == leftLocation) {
          json::object newEdge = edgeObj; // copy edge, we'll modify and add it back as a new edge
          newEdge["location"] = locationName;
          addEdgeToAutomaton(newEdge);
        }


        if (source == rightLocation) {
          json::object newEdge = edgeObj; // copy edge, we'll modify and add it back as a new edge
          newEdge["location"] = locationName;
          addEdgeToAutomaton(newEdge);
        }
      }

      return {locationName, {}};
    } else if(is_process_instance(expr)) {

      auto instance = down_cast<process_instance>(expr);

      // set current process name
      currentProcessName = pp(instance.identifier());

      auto eq = lookup_process_equation(instance.identifier());
      auto processExpr = eq.expression();

      vector<jani_var_name> lhs;
      vector<json::value> rhs;
      json::array pendingAssignments;

      for (const auto& arg : instance.actual_parameters()) {
        rhs.push_back(convert_data_expression(arg));
      }

      // register process params in symbol table
      // and get lhs for the instance's pending assignments
      enterProcessScope();
      variable_list params = eq.formal_parameters();
      for (auto& param : params) {
        lhs.push_back(registerVar(param, pp(eq.identifier()), true));
      }

      assert(lhs.size() == rhs.size());
      for (size_t i = 0; i < lhs.size(); ++i) {
        pendingAssignments.push_back(
          json::object{
            {"ref", lhs[i]},
            {"value", rhs[i]},
            {"index", 0}
          });
      }

      auto [innerProcessLocation, innerPendingAssignments] = translateProcessExpression(processExpr);

      // combine all assignments
      innerPendingAssignments.push_front(pendingAssignments);

      leaveScope();

      return {innerProcessLocation, innerPendingAssignments};
      
    } else if(is_sum(expr)) {
      // NOTE: - if we do create a location for this sum, i.e it's the first time we see it,
      //       this location will be overwritten. 
      //       - the snippet below will, upon seeing this sum again, return the location for the body, 
      //       since that's the location we set for this sum right after translating the body.
      auto [locationName, created] = ensureLocationForExpression(symExpr);
      if (!created) {
        return {locationName, {}};
      }

      auto sumExpr = down_cast<sum>(expr);

      enterScope();
      for (auto& var : sumExpr.variables()) {
        registerVar(var, currentProcessName);
      }

      auto [innerProcessLocation, pendingAssignments] = translateProcessExpression(sumExpr.operand());

      // copy all outgoing edges from the inner process location to this location, as sums don't have their own behavior, they just introduce new variables
      for (auto& edge : jani_automaton["edges"].as_array()) {
        auto& edgeObj = edge.as_object();
        auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
        auto source = edgeObj["location"].as_string().c_str();
        if (source == innerProcessLocation) {
          json::object newEdge = edgeObj; // copy edge, we'll modify and add it back as a new edge
          newEdge["location"] = locationName;
          addEdgeToAutomaton(newEdge);
        }
      }

      leaveScope();

      return {locationName, pendingAssignments};
    } else if(is_if_then(expr)) {
      auto [locationName, created] = ensureLocationForExpression(symExpr);
      if (!created) {
        return {locationName, {}};
      }
      auto ifThenExpr = down_cast<if_then>(expr);
      // for each outgoing edge from the inner process location, copy it and add aguard with the condition
      auto [innerLocation, pendingAssignments] = translateProcessExpression(ifThenExpr.then_case());

      // TODO: handle pending assignments while copying edges
      for (auto& edge : jani_automaton["edges"].as_array()) {
        auto& edgeObj = edge.as_object();
        auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
        auto source = edgeObj["location"].as_string().c_str();

        if (source == innerLocation) {
          json::object newEdge = edgeObj; // copy edge, we'll modify and add it back as a new edge
          newEdge["location"] = locationName;
          json::value guardExpression = convert_data_expression(ifThenExpr.condition());
          newEdge["guard"] = json::object({{"exp", guardExpression}});
          addEdgeToAutomaton(newEdge);
        }
      }

      return {locationName, {}};
    }  else {
      throw jani_translation_error("Unsupported process expression encountered during translation.");
    }
  }

  public:
    pcrl_to_automaton_translator(process::process_specification spec, const process_instance& initial_process_call, string automatonName, incomplete_edge_assignments incompleteEdgeAssignments)
    : initial_process_call(initial_process_call), incompleteEdgeAssignments(incompleteEdgeAssignments)
    {
      this->spec = spec;


      readingActions = readingActionSet({});

      jani_automaton = {
        {"name", automatonName},
        {"locations", json::array()},
        {"edges", json::array()}
      };
    }

    readingActionSet getReadingActions() const {
      return readingActions;
    }

    void removeUnreachableLocationsAndEdges(string initialLocation) {
      set<string> reachableLocations;
      
      // perform a DFS from the initial location to find all reachable locations
      vector<string> stack = {initialLocation};
      while (!stack.empty()) {
        string location = stack.back();
        stack.pop_back();
        if (!reachableLocations.contains(location)) {
          reachableLocations.insert(location);
          for (auto& edge : jani_automaton["edges"].as_array()) {
            auto& edgeObj = edge.as_object();
            auto source = edgeObj["location"].as_string().c_str();
            if (source == location) {
              auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
              stack.push_back(target);
            }
          }
        }
      }

      // remove locations that are not reachable
      // iterators are invalidated when we erase, so we first collect the locations to remove and then remove them in a second loop
      auto& locations = jani_automaton["locations"].as_array();
      set<string> locationsToRemove;
      for (auto it = locations.begin(); it != locations.end(); it++) {
        auto& locationObj = it->as_object();
        auto locationName = locationObj["name"].as_string().c_str();
        if (!reachableLocations.contains(locationName)) {
          locationsToRemove.insert(locationName);
        }
      }
      for (const auto& locationName : locationsToRemove) {
        eraseStateByName(locationName);
      }

      // remove edges that have an unreachable source or target
      auto& edges = jani_automaton["edges"].as_array();
      vector<json::value> edgesToRemove;
      for (auto it = edges.begin(); it != edges.end(); ) {
        auto& edgeObj = it->as_object();
        auto source = edgeObj["location"].as_string().c_str();
        auto target = edgeObj["destinations"].as_array()[0].as_object()["location"].as_string().c_str();
        if (!reachableLocations.contains(source) || !reachableLocations.contains(target)) {
          edges.erase(it);
          edges = jani_automaton["edges"].as_array();
          it = edges.begin(); // refresh iterator as erasing invalidates it
          continue;
        }
        it++;
      }
    }

    json::object translate(){

      auto [initialLocation, pendingAssignments] = translateProcessExpression(initial_process_call);

      jani_automaton["initial-locations"] = json::array({initialLocation});

      jani_automaton["variables"] = localVariables;

      // TODO: use the pending assignments to set initial values for local variables

      removeUnreachableLocationsAndEdges(initialLocation);

      return jani_automaton;
    };
};

using sync_vector = pair<vector<string>, multiset<string>>;
using inner_matrix = vector<sync_vector>;

class syncs_matrix {
  // vector of rows, in which each row has a left-hand side of ordered actions
  // and a right-hand side of a multiset of actions.

  private:

    syncs_matrix(const inner_matrix& m)
      : matrix(m)
    {}


  public:
  inner_matrix matrix;

  string pp_action_vector(vector<string> actions) {
    string s="[";
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
          "is illegal as there are reading actions involved but also none, or more than one writing action."

        );
      }

      if (row.second.size() > 1) {
        throw jani_translation_error(
          "Synchronization " + pp_action_vector(row.first) + " | " + formatResult(row.second) + " "
          "is illegal, all multiactions should be part of a communication. If this multiaction does not serve any "
          "purpose in your model, please disallow it."
        );
      }
    }
    
  }

  string formatResult(multiset<string> multiAction) {
    string serializedMultiAction;
    
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

  json::value getResult(multiset<string> multiAction, set<string>& jani_multiactions_set) {
    string serializedMultiAction = formatResult(multiAction);
    
    if (multiAction.size() > 1) {
      jani_multiactions_set.insert(serializedMultiAction);
    }

    return json::value(serializedMultiAction);
  }

  json::array getSynchronisation(vector<string> actions) {
    json::array synch;

    for (const auto& action : actions) {
      if (action == "null") {
        synch.push_back(json::value(nullptr));
      } else {
        synch.push_back(json::value(action));
      }
    }

    return synch;
  }

  json::array toJsonArray(set<string>& jani_multiactions_set) {
      json::array jsonArray;

      for (const auto& row : matrix) {
        jsonArray.push_back(
          json::object{
            {"synchronise", getSynchronisation(row.first)},
            {"result", getResult(row.second, jani_multiactions_set)}
          }
        );
      }

      return jsonArray;
    }
  syncs_matrix(vector<string> actions) {
    for (const auto& action : actions) {
      matrix.push_back(
        make_pair(
          vector<string>{action},
          multiset<string>{action}
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
        vector<string> newLHS = thisRow.first;
        newLHS.insert(newLHS.end(), otherRow.first.begin(), otherRow.first.end());

        // add multisets on right-hand sides
        multiset<string> newRHS = thisRow.second;
        newRHS.insert(otherRow.second.begin(), otherRow.second.end());

        newMatrix.push_back(
          make_pair(
            newLHS,
            newRHS
          )
        );
      }
    }
    return syncs_matrix(newMatrix);
  }

  syncs_matrix hide(const set<string>& actionsToHide) {

    for(const auto& action : actionsToHide) {
      // delete action from all multiactions possible in order to make them invisible / internal
      // Note: when a multiset end up empty, this should signify a tau action.
      for (auto& row : matrix) {
        row.second.erase(action);
      }
    }
    return *this;
  }

  syncs_matrix rename(const map<string, string>& renamings) {
    for(auto& renaming : renamings) {
      const string& from = renaming.first;
      const string& to = renaming.second;

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

  syncs_matrix comm(const set<pair<multiset<string>, string>>& comms) {

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
  syncs_matrix allow(const set<multiset<string>>& multiactionsToAllow) {
    for (auto row = matrix.begin(); row != matrix.end(); ) {
      if (multiactionsToAllow.contains(row->second)) {
        ++row;
      } else {
        row = matrix.erase(row);
      }
    }
    return *this;
  }
  syncs_matrix block(const set<string>& actionsToBlock) {
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
  map<process_identifier, uint> automatonCounters;
  // gets all process identifiers that are reachable from the initial process
  // for now assumed to be pcrl
  multiset<process_instance> collectPcrlProcessesRec(const process_expression& expr) {
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
      mCRL2log(mcrl2::log::info) << "Unsupported process expression: " << process::pp(expr) << endl;
      throw jani_translation_error("Unsupported process expression encountered during pCRL process collection.");
    }
  }
  multiset<process_instance> collectPcrlProcesses() {
    auto initialProcess = spec.init();

    return collectPcrlProcessesRec(initialProcess);
  }

  syncs_matrix buildSyncsMatrixRec(const process_expression& expr) {
    if (is_process_instance(expr)) {
      // base case: single process instance
      vector<string> actionsVector;
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
        set<multiset<string>> actionsToAllow;
        for (const auto& multiAction : allowedActions) {
          multiset<string> multiActionToInsert;
          for (const auto& action : multiAction.names()) {
            mCRL2log(mcrl2::log::info) << "Allowing action in syncs matrix: " << pp(action) << endl;
            multiActionToInsert.insert(pp(action));

          }
          actionsToAllow.insert(multiActionToInsert);
        }
        auto subMatrix = buildSyncsMatrixRec(process::allow(expr).operand());
        return subMatrix.allow(actionsToAllow);
    } else if (is_block(expr)) {
      auto blockedActions = process::block(expr).block_set();
      set<string> actionsToBlock;
      for (const auto& action : blockedActions) {
        mCRL2log(mcrl2::log::info) << "Blocking action in syncs matrix: " << pp(action) << endl;
        actionsToBlock.insert(pp(action));
      }
      auto subMatrix = buildSyncsMatrixRec(process::block(expr).operand());
      return subMatrix.block(actionsToBlock);
    } else if (is_hide(expr)) {
      auto hiddenActions = process::hide(expr).hide_set();
      set<string> actionsToHide;
      for (const auto& action : hiddenActions) {
        mCRL2log(mcrl2::log::info) << "Hiding action in syncs matrix: " << pp(action) << endl;
        actionsToHide.insert(pp(action));
      }
      auto subMatrix = buildSyncsMatrixRec(process::hide(expr).operand());
      return subMatrix.hide(actionsToHide);
    } else if (is_rename(expr)) {
      auto renamingList = process::rename(expr).rename_set();
      map<string, string> renamings;
      for (const auto& renaming : renamingList) {
        mCRL2log(mcrl2::log::info) << "Renaming action in syncs matrix: " << pp(renaming.source()) << " to " << pp(renaming.target()) << endl;
        renamings[pp(renaming.source())] = pp(renaming.target());
      }
      auto subMatrix = buildSyncsMatrixRec(process::rename(expr).operand());
      return subMatrix.rename(renamings);
    } else if (is_comm(expr)) {
      auto commSet = process::comm(expr).comm_set();
      set<pair<multiset<string>, string>> actionsToComm;
      for (const auto& commExp : commSet) {
        multiset<string> commLHS;
        for (const auto& action : commExp.action_name().names()) {
          commLHS.insert(pp(action));
        }
        actionsToComm.insert(make_pair(commLHS, pp(commExp.name())));
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
  json::object translate_process_equation(const process_instance& procInst) {

    mCRL2log(mcrl2::log::info) << "Translating process equation for: " << process::pp(procInst) << endl;

    string automatonName;
    if (automatonCounters.find(procInst.identifier()) == automatonCounters.end()) {
      automatonCounters[procInst.identifier()] = 0;
      automatonName = pp(procInst.identifier());
    } else {
      automatonName = pp(procInst.identifier()) + to_string(automatonCounters[procInst.identifier()]);
      automatonCounters[procInst.identifier()]++;
    }

    pcrl_to_automaton_translator translator(spec, procInst, automatonName, incompleteEdgeAssignments);
    auto automaton = translator.translate();
    auto automatonReadingActions = translator.getReadingActions();
    readingActions.insert(automatonReadingActions.begin(), automatonReadingActions.end());
    return automaton;
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


          jani_variables.push_back(json::object(
            {
              {"name", actionName + "_" + to_string(i)},
              {"transient", true},
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
        json::object{
          {"name", pp(actionLabel)}
        }
      );
    }
  }


public:
  json::object jani_model;
  json::array jani_actions;
  set<string> jani_multiactions_set;
  json::array jani_variables;
  json::array jani_automata;
  json::array jani_edges;
  json::array jani_system_elements;

  process::process_specification spec;

  // constructor
  jani_translator(const process::process_specification& specification)
    : spec(specification) {
      readingActions = readingActionSet();
    }

  

  json::object translate_process_specification()
  {

    multiset<process_instance> prclProcesses = collectPcrlProcesses();
    translateActions();
    auto syncsMatrix = buildSyncsMatrix();

    for (const auto& procInst : prclProcesses) {
      // cout << "Found pCRL process: " << process::pp(procInst) << endl;

      jani_system_elements.push_back(
          json::value({{"automaton", pp(procInst.identifier())}})
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
    //     json::object{
    //       {"name", multiaction}
    //     }
    //   );
    // }

    addTransientVars();

    addMissingAssignments(syncsMatrix);

    return json::object(
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

  void addMissingAssignments(syncs_matrix syncsMatrix) {
    // first compute the map writing action -> list of reading actions
    json::array newJaniAutomata;
    
    map<string, set<string>> writeToReads;
    for (auto& sync : syncsMatrix.matrix) {

      string writingAction;
      set<string> mappedReadingActions;

      for (auto& actionName : sync.first) {
        if (readingActions.contains(actionName)) {
          mappedReadingActions.insert(actionName);
        } else {
          writingAction = actionName;
        }
      }

      writeToReads[writingAction].insert(mappedReadingActions.begin(), mappedReadingActions.end());
    }


    // now add missing assignments on every automaton edge that executes a writing action.

    for (auto& automaton : jani_automata) {
      auto edgesV = automaton.at_pointer("/edges");
      assert(edgesV.is_array());
      auto edges = edgesV.as_array();

      json::array newEdges;

      for (auto& edgeV : edges) {
        auto edge = edgeV.as_object();
        string actionName;


        bool isWritingAction = edge.contains("action") && edge.at("action").is_string() && !readingActions.contains(actionName = edge.at("action").as_string().c_str());
        auto destination = (edge.at("destinations").as_array()[0]).as_object();
        bool hasAssignments = destination.contains("assignments") && destination.at("assignments").is_array() && destination.at("assignments").as_array().size() > 0;
        if (isWritingAction && hasAssignments) {
          json::object newEdge = edge;
          json::array newAssignments;
          // newEdge["action"] = actionName;
          // newEdge["location"] = edge["location"];

          for (uint i = 0; i < destination.at("assignments").as_array().size(); i++) {
            string oldRef = destination.at("assignments").at(i).at("ref").as_string().c_str();

            // variables won't have a digit as a first character
            // this way we know this is a writing actions assignment
            for (auto& readAction : writeToReads[actionName]) {
              auto newAssignment = destination.at("assignments").at(i).as_object();

              // if edge executes writing action, then add missing assignments
              if(isdigit(oldRef[0])) {
                string ref = readAction + "_" + oldRef; 
                json::value val = destination.at("assignments").at(i).at("value");

                newAssignment["ref"] = ref;
                newAssignment["value"] = val;
              }

              newAssignments.push_back(newAssignment);

              // newAssignments.push_back(json::object({
              //   {"value", val},
              //   {"ref", ref}
              // }));
            }
          }

          destination["assignments"] = newAssignments;
          newEdge["destinations"] = json::array({destination});
          newEdges.push_back(newEdge);
          
        } else {
          newEdges.push_back(edge);
        }
      }
      automaton.at_pointer("/edges") = newEdges;
      newJaniAutomata.push_back(automaton);
    }

    jani_automata = newJaniAutomata;
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
      mCRL2log(mcrl2::log::verbose) << "Reading input from stdin..." << endl;
      spec = mcrl2::process::parse_process_specification(cin);
    }
    else
    {
      mCRL2log(mcrl2::log::verbose) << "Reading input from file '" << input_filename() << "'..." << endl;
      ifstream instream(input_filename().c_str(), ifstream::in | ifstream::binary);
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
      mCRL2log(mcrl2::log::info) << "stdin contains a well-formed mCRL2 specification" << endl;
    }
    else
    {
      mCRL2log(mcrl2::log::info) << "the file '" << input_filename() << "' contains a well-formed mCRL2 specification"
                                 << endl;
    }

    mCRL2log(mcrl2::log::info) << mcrl2::process::pp(spec, false) << endl;

    // check that spec is linearisable
    // mcrl2::lps::stochastic_specification linear_spec(mcrl2::lps::linearise(spec, m_linearisation_options));
    jani_translator translator(spec);


    // cout << "Translating to JANI..." << endl;

    auto janiModel = translator.translate_process_specification();

    cout << janiModel << endl;

    return true;
  }
};

int main(int argc, char** argv)
{
  return mcrl22jani_tool().execute(argc, argv);
}
