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
#include "mcrl2/data/find.h"
#include "mcrl2/data/replace.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
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
#include "mcrl2/process/find.h"
#include "mcrl2/process/process_expression.h"
#include "mcrl2/process/replace.h"

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


class jani_translation_error : public mcrl2::runtime_error
{
  public:
  jani_translation_error(const string& message)
    : mcrl2::runtime_error(message)
  {}
};

using actionSet = set<string>;

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

using write_reads_map = map<string, vector<string>>;

// this type represents locations, whatever that is at the moment
// if L1 and L2 are of type abstract_location and they represent
// the same location in terms of our theory, then it should hold that
// L1 != L2
// Ensure the types used to define this type always make this hold or
// override behaviors as needed

// Sentinel location for successful termination (√). mCRL2's process_expression
// has no such constructor, so we add one here.
struct termination_t {
  auto operator<=>(const termination_t&) const = default;
};

// β (symbol map): binds each free (equation-parameter) variable of a location's
// process expression to the JANI variable name that represents it. It is part of
// a location's identity so that the same body term reused by different equations
// (e.g. a(n) in both P and Q) yields distinct locations with distinct JANI
// variables (P_n vs Q_n).
using symbol_map = std::map<data::variable, std::string>;

// env (substitution environment): the pending substitution [Asgn] of the thesis
// location triple Loc = ProcExp × (mCRL2Var → JANIVar) × [Asgn]. Maps free data
// variables to the expressions they stand for. At the data-without-communication
// stage it is empty in every reachable location (process-instance parameter passing
// is materialised onto edges, not kept here); it is carried in identity so that the
// Recursión/Fijación location p[d:=t] is representable and dedups correctly, and so
// dist-introduced substitutions distinguish locations once that operator lands.
using subst_env = std::map<data::variable, data::data_expression>;

// A non-terminating location: a process expression together with the symbol map
// (β) binding its free variables and the pending substitution environment (env).
// Identity (and BFS dedup) is structural over (expr, beta, env).
struct process_location {
  process_expression expr;
  symbol_map beta;
  subst_env env;
  auto operator<=>(const process_location&) const = default;
  bool operator==(const process_location&) const = default;
};

using abstract_location = std::variant<process_location, termination_t>;

class pcrl_to_automaton_translator{
private:

    string currentProcessName;
public:


  private:
    process::process_specification spec;
    json::object jani_automaton;
    const process_instance& initial_process_call;
    uint stateCounter = 0;
    json::object deltaLocation;

    // JANI variables discovered while exploring (jani name -> mCRL2 sort), built
    // from the symbol maps of the visited locations. Keyed by string so iteration
    // order is deterministic (never iterate aterm-keyed containers for output).
    std::map<std::string, data::sort_expression> jani_variable_sorts;

    const string DELTA_LOCATION_NAME = "delta_state";
    const string TERMINATION_LOCATION_NAME = "termination";


  json::object newState() {
    // TODO: add the state here and just return the name
    json::object state{
      {"name", "state_" + to_string(stateCounter)}
    };

    stateCounter++;

    return state;
  }

  
  void ensureDeltaLocation() {
    if (deltaLocation.empty()) {
      deltaLocation = json::object{
        {"name", DELTA_LOCATION_NAME}
      };
      addStateToAutomaton(deltaLocation);
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

  // computes the `destinations` to put in a transition
  // leading to process p
  json::array stoch(process_expression p) {
    // TODO: implement by structural recursion
    // NOTE: this won't need

    if (is_action(p)){

    } else if(is_delta(p)) {

    } else if (is_stochastic_operator(p)) {
      
    } else if (is_seq(p)) {

    } else if (is_choice(p)) {

    } else if (is_if_then(p)) {

    } else if (is_if_then(p)) {

    } else if (is_sum(p)) {

    } else if (is_process_instance(p)) {

    } else {
      throw jani_translation_error(
        "Expression " + pp(p) + " not supported by Stoch");
    }
  }

  // Helper function: Get maximum index from an assignment list
  // Returns -1 if the list is empty
  int get_max_index(const json::array& as) {
    int max_idx = -1;
    for (const auto& assignment : as) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        if (obj.contains("index")) {
          auto idx_val = obj.at("index");
          if (idx_val.is_int64()) {
            int idx = static_cast<int>(idx_val.as_int64());
            if (idx > max_idx) {
              max_idx = idx;
            }
          }
        }
      }
    }
    return max_idx;
  }

  // Helper function: Get minimum index from an assignment list
  // Returns INT_MAX if the list is empty
  int get_min_index(const json::array& as) {
    int min_idx = INT_MAX;
    for (const auto& assignment : as) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        if (obj.contains("index")) {
          auto idx_val = obj.at("index");
          if (idx_val.is_int64()) {
            int idx = static_cast<int>(idx_val.as_int64());
            if (idx < min_idx) {
              min_idx = idx;
            }
          }
        }
      }
    }
    return min_idx;
  }

  // coin(as1, as2): Find the set of variables assigned in both lists
  set<string> coin(const json::array& as1, const json::array& as2) {
    set<string> vars_as1;
    set<string> common;

    // Collect all variables in as1
    for (const auto& assignment : as1) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        if (obj.contains("ref")) {
          auto ref_val = obj.at("ref");
          if (ref_val.is_string()) {
            vars_as1.insert(string(ref_val.as_string()));
          }
        }
      }
    }

    // Find common variables in as2
    for (const auto& assignment : as2) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        if (obj.contains("ref")) {
          auto ref_val = obj.at("ref");
          if (ref_val.is_string()) {
            string var = string(ref_val.as_string());
            if (vars_as1.find(var) != vars_as1.end()) {
              common.insert(var);
            }
          }
        }
      }
    }

    return common;
  }

  // restrict_assignments(as, vs): Filter assignments to only those for variables in set vs
  json::array restrict_assignments(const json::array& as, const set<string>& vars) {
    json::array result;
    for (const auto& assignment : as) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        if (obj.contains("ref")) {
          auto ref_val = obj.at("ref");
          if (ref_val.is_string()) {
            string var = string(ref_val.as_string());
            if (vars.find(var) != vars.end()) {
              result.push_back(assignment);
            }
          }
        }
      }
    }
    return result;
  }

  // iconcat(as1, as2): Concatenate assignment lists with index shifting
  // - Indices of as2 are incremented by max(as1) + 1
  // - Variables appearing in both lists are excluded from the result
  json::array iconcat(const json::array& as1, const json::array& as2) {
    // Compute coin(as1, as2) - variables appearing in both
    set<string> common_vars = coin(as1, as2);

    // Get the maximum index from as1
    int max_idx_as1 = get_max_index(as1);
    int index_shift = max_idx_as1 + 1;

    json::array result;

    // Add all assignments from as1
    for (const auto& assignment : as1) {
      result.push_back(assignment);
    }

    // Add assignments from as2 with shifted indices, excluding common variables
    for (const auto& assignment : as2) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        string var;

        // Extract variable name
        if (obj.contains("ref")) {
          auto ref_val = obj.at("ref");
          if (ref_val.is_string()) {
            var = string(ref_val.as_string());
          }
        }

        // Skip if variable is in common set
        if (common_vars.find(var) != common_vars.end()) {
          continue;
        }

        // Create new assignment with shifted index
        json::object new_assignment;
        for (auto& [key, val] : obj) {
          if (key == "index" && val.is_int64()) {
            int old_idx = static_cast<int>(val.as_int64());
            new_assignment[key] = old_idx + index_shift;
          } else {
            new_assignment[key] = val;
          }
        }

        result.push_back(new_assignment);
      }
    }

    return result;
  }

  // iiconcat(as1, as2): Inverse concatenate assignment lists
  // - Indices of as1 are shifted backward to precede as2
  // - Variables appearing in both lists are excluded from the result
  json::array iiconcat(const json::array& as1, const json::array& as2) {
    // Compute coin(as1, as2) - variables appearing in both
    set<string> common_vars = coin(as1, as2);

    // Get max index from as1 and min index from as2
    int max_idx_as1 = get_max_index(as1);
    int min_idx_as2 = get_min_index(as2);

    // Calculate the shift for as1: indices should be shifted to make room for as2 after
    // Shift is: i - max_idx_as1 - min_idx_as2 - 1
    int shift_as1 = -max_idx_as1 - min_idx_as2 - 1;

    json::array result;

    // Add assignments from as1 with shifted indices, excluding common variables
    for (const auto& assignment : as1) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        string var;

        // Extract variable name
        if (obj.contains("ref")) {
          auto ref_val = obj.at("ref");
          if (ref_val.is_string()) {
            var = string(ref_val.as_string());
          }
        }

        // Skip if variable is in common set
        if (common_vars.find(var) != common_vars.end()) {
          continue;
        }

        // Create new assignment with shifted index
        json::object new_assignment;
        for (auto& [key, val] : obj) {
          if (key == "index" && val.is_int64()) {
            int old_idx = static_cast<int>(val.as_int64());
            new_assignment[key] = old_idx + shift_as1;
          } else {
            new_assignment[key] = val;
          }
        }

        result.push_back(new_assignment);
      }
    }

    // Add all assignments from as2
    for (const auto& assignment : as2) {
      result.push_back(assignment);
    }

    return result;
  }

  // Shifts every assignment index by a constant so the minimum becomes 0, preserving
  // the relative order and the equal-index (simultaneous) groups. ++_* (iiconcat) can
  // produce negative indices; JANI assignment indices are emitted non-negative.
  json::array normalizeAssignmentIndices(const json::array& as) {
    if (as.empty()) {
      return as;
    }
    int min_idx = get_min_index(as);
    if (min_idx == 0) {
      return as;
    }
    json::array result;
    for (const auto& assignment : as) {
      if (assignment.is_object()) {
        json::object obj = assignment.as_object();
        if (obj.contains("index") && obj.at("index").is_int64()) {
          obj["index"] = static_cast<int>(obj.at("index").as_int64()) - min_idx;
        }
        result.push_back(obj);
      } else {
        result.push_back(assignment);
      }
    }
    return result;
  }

  // apply_assignments(as, expr): Apply an assignment list as substitution to an expression
  // This function applies the variable assignments from the assignment list to the expression
  // Variables are substituted with their assigned values in order of their indices
  json::value apply_assignments(const json::array& as, json::value expr) {
    // Build a substitution map from the assignment list
    // Sort assignments by index to apply them in the correct order
    vector<pair<int, pair<string, json::value>>> sorted_assignments;

    for (const auto& assignment : as) {
      if (assignment.is_object()) {
        auto obj = assignment.as_object();
        string var;
        json::value value;
        int index = 0;

        if (obj.contains("ref") && obj.at("ref").is_string()) {
          var = string(obj.at("ref").as_string());
        }
        if (obj.contains("value")) {
          value = obj.at("value");
        }
        if (obj.contains("index") && obj.at("index").is_int64()) {
          index = static_cast<int>(obj.at("index").as_int64());
        }

        if (!var.empty()) {
          sorted_assignments.push_back({index, {var, value}});
        }
      }
    }

    // Sort by index using a custom comparator
    sort(sorted_assignments.begin(), sorted_assignments.end(),
         [](const pair<int, pair<string, json::value>>& a,
            const pair<int, pair<string, json::value>>& b) {
           return a.first < b.first;
         });

    // Apply substitutions in order
    json::value result = expr;
    for (const auto& [idx, var_val] : sorted_assignments) {
      const string& var = var_val.first;
      const json::value& value = var_val.second;

      // Recursively substitute the variable in the expression
      // For now, simple substitution in json structures
      result = substitute_in_expression(result, var, value);
    }

    return result;
  }

private:
  // Helper function: Recursively substitute a variable in a JSON expression
  json::value substitute_in_expression(const json::value& expr, const string& var, const json::value& value) {
    if (expr.is_object()) {
      json::object result;
      auto obj = expr.as_object();

      for (auto& [key, val] : obj) {
        if (key == "ref" && val.is_string() && string(val.as_string()) == var) {
          result[key] = value;
        } else {
          result[key] = substitute_in_expression(val, var, value);
        }
      }
      return result;
    } else if (expr.is_array()) {
      json::array result;
      auto arr = expr.as_array();
      for (const auto& elem : arr) {
        result.push_back(substitute_in_expression(elem, var, value));
      }
      return result;
    } else {
      return expr;
    }
  }

public:

  // Converts an mCRL2 data expression to a JANI expression (JSON), resolving free
  // variables through the symbol map β. JANI lacks > and >=, so those are flipped
  // to < and ≤. Data on actions and the reading/writing machinery are out of scope
  // here. Unsupported sorts/operators raise jani_translation_error.
  json::value convert_data_expression(const data::data_expression& e, const symbol_map& beta)
  {
    if (is_variable(e))
    {
      const data::variable& v = atermpp::down_cast<data::variable>(e);
      auto it = beta.find(v);
      if (it == beta.end())
      {
        throw jani_translation_error("Free variable " + pp(v) + " has no JANI binding "
          "(not an equation parameter in scope).");
      }
      return json::value(it->second);
    }
    else if (data::sort_bool::is_true_function_symbol(e))
    {
      return true;
    }
    else if (data::sort_bool::is_false_function_symbol(e))
    {
      return false;
    }
    else if (data::sort_pos::is_positive_constant(e) ||
             data::sort_nat::is_natural_constant(e) ||
             data::sort_int::is_integer_constant(e))
    {
      return std::stoll(pp(e));
    }
    else if (data::sort_bool::is_not_application(e))
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"op", reinterpret_cast<const char*>(u8"¬")},
        {"exp", convert_data_expression(appl[0], beta)}
      };
    }
    else if (is_greater_application(e)) // > is unsupported in JANI; flip to <
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"left", convert_data_expression(appl[1], beta)},
        {"op", "<"},
        {"right", convert_data_expression(appl[0], beta)}
      };
    }
    else if (is_greater_equal_application(e)) // >= is unsupported in JANI; flip to <=
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"left", convert_data_expression(appl[1], beta)},
        {"op", reinterpret_cast<const char*>(u8"≤")},
        {"right", convert_data_expression(appl[0], beta)}
      };
    }
    else if (data::sort_bool::is_implies_application(e))
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);
      return json::object{
        {"op", "ite"},
        {"if", convert_data_expression(appl[0], beta)},
        {"then", convert_data_expression(appl[1], beta)},
        {"else", true}
      };
    }
    else if (data::is_application(e))
    {
      const data::application& appl = atermpp::down_cast<data::application>(e);

      // Identity coercions between numeric sorts: JANI has a single numeric tower,
      // so e.g. Int2Nat(x) is just x.
      static const std::set<std::string> coercions = {
        "Int2Nat", "Nat2Int", "Pos2Nat", "Nat2Pos", "Int2Pos", "Pos2Int",
        "Int2Real", "Nat2Real", "Pos2Real", "Real2Int"
      };
      if (appl.size() == 1 && coercions.contains(pp(appl.head())))
      {
        return convert_data_expression(appl[0], beta);
      }
      // Unary floor/ceil pass through with their operator name.
      if (appl.size() == 1 &&
          (data::sort_real::is_floor_application(e) || data::sort_real::is_ceil_application(e)))
      {
        return json::object{
          {"op", pp(appl.head())},
          {"exp", convert_data_expression(appl[0], beta)}
        };
      }
      // Binary operators: left <op> right.
      if (appl.size() == 2)
      {
        return json::object{
          {"left", convert_data_expression(appl[0], beta)},
          {"op", convert_operator_to_jani(appl.head())},
          {"right", convert_data_expression(appl[1], beta)}
        };
      }
      throw jani_translation_error("Unsupported data expression (arity " +
        std::to_string(appl.size()) + "): " + pp(e) + ".");
    }
    else
    {
      throw jani_translation_error("Jani does not support the main operator in the "
        "expression " + pp(e) + ".");
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

  void strengthenGuardOfEdge(json::object& edge, json::value guardExpression) {
    if (edge.contains("guard")) {
      auto newGuardExpression = json::object{
        {"op", reinterpret_cast<const char*>(u8"∧")},
        {"left", edge["guard"].as_object().at("exp")},
        {"right", guardExpression}
      };
      edge["guard"] = json::object{
        {"exp", newGuardExpression}
      };
    } else {
      edge["guard"] = json::object{
        {"exp", guardExpression}
      };
    }
  }

  // Negates a guard expression
  json::object negateGuardExpression(json::value guardExpression) {
    if (guardExpression.is_object() && guardExpression.as_object().contains("op") && guardExpression.at("op").as_string().c_str() == "¬") {
      return guardExpression.at("exp").as_object();
    } else {
      return json::object{
        {"op", reinterpret_cast<const char*>(u8"¬")},
        {"exp", guardExpression}
      };
    }
  }


  public:
    pcrl_to_automaton_translator(process::process_specification spec, const process_instance& initial_process_call, string automatonName)
    : initial_process_call(initial_process_call)
    {
      this->spec = spec;

      jani_automaton = {
        {"name", automatonName},
        {"locations", json::array()},
        {"edges", json::array()}
      };
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

    using transition = pair<json::object /* edge */, abstract_location>;

    // Wraps a process expression with its symbol map (β) and substitution
    // environment (env) into a location. β and env are restricted to the *free*
    // variables of `e` (thesis: "β binds its free variables"): this canonicalises
    // identity so that two paths reaching the same sub-term through different outer
    // scopes — which may carry unused bindings merged in by e.g. seqTarget — dedup to
    // one location and render to one name, instead of staying distinct yet colliding.
    abstract_location makeLoc(const process_expression& e, const symbol_map& beta,
                              const subst_env& env = {}) {
      std::set<data::variable> fv = process::find_free_variables(e);
      // env binds the formals free in e; its RHS expressions may reference
      // further-out variables (when the substitution is not yet ground), whose β
      // bindings must be retained so the RHS can be converted later.
      subst_env restrictedEnv;
      std::set<data::variable> keep = fv;
      for (const auto& [v, expr] : env) {
        if (fv.count(v) != 0u) {
          restrictedEnv[v] = expr;
          std::set<data::variable> rhsFv = data::find_free_variables(expr);
          keep.insert(rhsFv.begin(), rhsFv.end());
        }
      }
      symbol_map restrictedBeta;
      for (const auto& [v, name] : beta) {
        if (keep.count(v) != 0u) {
          restrictedBeta[v] = name;
        }
      }
      return process_location{e, restrictedBeta, restrictedEnv};
    }

    // β for an equation: each formal parameter is bound to a JANI variable named
    // "<Process>_<param>", so parameters of different equations never clash.
    symbol_map makeBeta(const process_identifier& id, const data::variable_list& params) {
      symbol_map beta;
      string prefix = pp(id.name());
      for (const auto& v : params) {
        beta[v] = prefix + "_" + pp(v.name());
      }
      return beta;
    }

    // Maps an abstract location to its JANI location name. The name renders the
    // process expression with each free variable replaced by the JANI variable name β
    // assigns it (and by its env expression where present), so that distinct locations
    // that share a process sub-term get distinct names: e.g. b(n) under β:n↦P_n vs
    // n↦Q_n becomes "b(P_n)" vs "b(Q_n)" instead of colliding on pp(expr). Because
    // makeLoc restricts β/env to the free variables of expr, the rendered name is a
    // function of the full (expr, β, env) identity.
    string locationName(const abstract_location& loc) {
      if (std::holds_alternative<termination_t>(loc)) {
        return TERMINATION_LOCATION_NAME;
      }
      const process_location& pl = std::get<process_location>(loc);
      data::mutable_map_substitution<> sigma;
      for (const auto& [v, name] : pl.beta) {
        sigma[v] = data::variable(mcrl2::core::identifier_string(name), v.sort());
      }
      // env (when non-empty) substitutes the variable away entirely, so it takes
      // precedence over β. Single pass, no recursion into the RHS (cf. thesis psub).
      for (const auto& [v, expr] : pl.env) {
        sigma[v] = expr;
      }
      return pp(process::replace_variables(pl.expr, sigma));
    }

    // Re-sources every edge of `transitions` to `newSource` (in place) and returns
    // them. Composite operators use this to attribute a sub-expression's
    // transitions to the enclosing location.
    list<transition> reSource(list<transition> transitions, const string& newSource) {
      for (auto& [edge, target] : transitions) {
        edge["location"] = newSource;
      }
      return transitions;
    }

    // Target of a sequential composition p·q given a transition of p reaching
    // `target`: q if p terminated (Seq-2), else target·q (Seq-1). The merged β
    // covers both target's free variables and q's (their JANI names never clash).
    abstract_location seqTarget(const abstract_location& target,
                                const process_expression& right, const symbol_map& beta) {
      if (std::holds_alternative<termination_t>(target)) {
        return makeLoc(right, beta);
      }
      const process_location& tpl = std::get<process_location>(target);
      symbol_map merged = beta;
      merged.insert(tpl.beta.begin(), tpl.beta.end());
      return makeLoc(seq(tpl.expr, right), merged);
    }

    // env as an mCRL2 substitution, for rewriting guards (and actuals) before
    // conversion. Single-pass / no recursion into RHS, matching the thesis psub.
    data::mutable_map_substitution<> toSubst(const subst_env& env) {
      data::mutable_map_substitution<> s;
      for (const auto& [v, e] : env) {
        s[v] = e;
      }
      return s;
    }

    // Result of entering a process instance P(actual) while in scope (β, env) with
    // the given head-chain `pending` assignments: the body is explored as the
    // first-class (but never stored) location (eqn.expression(), mergedBeta, newEnv).
    struct instance_entry {
      symbol_map mergedBeta;   // β ∪ βP, callee winning on same-named formals
      subst_env newEnv;        // {formalᵢ ↦ psub(actualᵢ, env)} — drives the body's guards
      json::array newPending;  // pending ++_* {βP(formalᵢ) := convert(actualᵢ)} — edge asgns
    };

    // Builds the scope for the body of P(actual) per the Fijación/Recursión rules.
    // Two distinct jobs (thesis: c' = as(c) and W' = as ++_* bs):
    //  - newEnv composes the substitution into the actuals, so the body's GUARDS resolve
    //    to ground / already-committed values (a guard cannot read a var assigned on the
    //    same edge);
    //  - newPending carries the EDGE assignments with the actuals left SYMBOLIC
    //    (βP(formalᵢ) := convert(actualᵢ)) and is merged via ++_* (iiconcat) so an outer
    //    instance's assignments get a strictly lower index and run first. The body's tail
    //    instances stay symbolic, referencing the βP variables these assignments set.
    instance_entry enterInstance(const process_identifier& id, const process_equation& eqn,
                                 const data::data_expression_list& actuals,
                                 const symbol_map& beta, const subst_env& env,
                                 const json::array& pending) {
      symbol_map betaP = makeBeta(id, eqn.formal_parameters());
      // Callee bindings win for formals sharing a name+sort across equations.
      symbol_map mergedBeta = beta;
      for (const auto& [v, name] : betaP) {
        mergedBeta[v] = name;
      }
      data::mutable_map_substitution<> envSubst = toSubst(env);
      subst_env newEnv;
      // This instance's parameter assignments, all at index 0 (simultaneous — so e.g.
      // P(x,y) = … P(y,x) is a correct swap). Values are left symbolic.
      json::array currentLayerAs;
      auto fit = eqn.formal_parameters().begin();
      auto ait = actuals.begin();
      for (; fit != eqn.formal_parameters().end() && ait != actuals.end(); ++fit, ++ait) {
        // Guards: compose the substitution into the actual (resolve to ground/committed).
        newEnv[*fit] = data::replace_variables(*ait, envSubst);
        // Declare the target JANI variable (an unused parameter is free in no stored
        // location, so collectVariables would otherwise miss it).
        jani_variable_sorts[betaP.at(*fit)] = fit->sort();
        // Edge assignment: actual kept symbolic, resolved only through β.
        currentLayerAs.push_back(json::object{
          {"ref", betaP.at(*fit)},
          {"value", convert_data_expression(*ait, mergedBeta)},
          {"index", 0}
        });
      }
      // ++_*: outer (pending) assignments get the lower indices and run first; for a
      // single (non-nested) instance pending is empty and iiconcat is the identity.
      json::array newPending = iiconcat(pending, currentLayerAs);
      return instance_entry{mergedBeta, newEnv, newPending};
    }

    // Computes the outgoing transitions of a location. PURE: it does not touch the
    // automaton, so it can recurse through composite operators without materialising
    // states. Committing happens in translateProcessExpression.
    //
    // Returns (edge, location) pairs; every edge has source = locationName(loc).
    // successors is the SOS transition relation (→); a termination_t encodes ✓.
    list<transition> successors(const abstract_location& loc) {
      std::set<process_identifier> unfolding;
      return successors(loc, unfolding);
    }

    // `unfolding` tracks the process identifiers expanded in the current
    // action-free head position, to reject unguarded recursion (e.g. P = P). It is
    // taken by value so sibling branches explore independently.
    list<transition> successors(const abstract_location& loc, std::set<process_identifier> unfolding,
                                json::array pending = json::array({})) {
      list<transition> result;

      // termination is a sink: no outgoing transitions.
      if (std::holds_alternative<termination_t>(loc)) {
        return result;
      }

      const process_location& pl = std::get<process_location>(loc);
      const process_expression& expr = pl.expr;
      const symbol_map& beta = pl.beta;
      // The head-chain substitution since the last action: resolves guards (env) and
      // is materialised on this step's action edge (pending). Both reset across an
      // action — tails reached via seqTarget are env-free and start with empty pending.
      const subst_env& env = pl.env;

      // (Act)  a(d) ──a──▶ ✓   (data arguments deferred); the head-chain parameter
      // assignments accumulated in `pending` are emitted on this edge.
      if (is_action(expr)) {
        const process::action& act = atermpp::down_cast<process::action>(expr);
        json::object edge = makeEdge(locationName(loc), TERMINATION_LOCATION_NAME, pp(act.label()),
                                     normalizeAssignmentIndices(pending));
        result.push_back({edge, termination_t{}});
      }
      // (Delta)  δ : deadlock, no transitions.
      else if (is_delta(expr)) {
        // no successors
      }
      // (Choice-L/R)
      else if (is_choice(expr)) {
        const process::choice& choiceExpr = atermpp::down_cast<process::choice>(expr);
        result.splice(result.end(), reSource(successors(makeLoc(choiceExpr.left(), beta, env), unfolding, pending), locationName(loc)));
        result.splice(result.end(), reSource(successors(makeLoc(choiceExpr.right(), beta, env), unfolding, pending), locationName(loc)));
      }
      // (Seq-1) p·q ──a──▶ p'·q   (Seq-2) p ──a──▶ ✓ ⟹ p·q ──a──▶ q
      else if (is_seq(expr)) {
        const seq& sequence = atermpp::down_cast<seq>(expr);
        const process_expression& right = sequence.right();

        for (auto& [edge, target] : successors(makeLoc(sequence.left(), beta, env), unfolding, pending)) {
          abstract_location newTarget = seqTarget(target, right, beta);
          edge["location"] = locationName(loc);
          edge["destinations"].as_array()[0].as_object()["location"] = locationName(newTarget);
          result.push_back({edge, newTarget});
        }
      }
      // (Cond1)  c -> p : guard p's transitions with c (deadlock when ¬c)
      else if (is_if_then(expr)) {
        const if_then& cond = atermpp::down_cast<if_then>(expr);
        data::mutable_map_substitution<> envSubst = toSubst(env);
        json::value guard = convert_data_expression(data::replace_variables(cond.condition(), envSubst), beta);
        for (auto& [edge, target] : reSource(successors(makeLoc(cond.then_case(), beta, env), unfolding, pending), locationName(loc))) {
          strengthenGuardOfEdge(edge, guard);
          result.push_back({edge, target});
        }
      }
      // (Cond2)  c -> p <> q : p guarded by c, q guarded by ¬c
      else if (is_if_then_else(expr)) {
        const if_then_else& cond = atermpp::down_cast<if_then_else>(expr);
        data::mutable_map_substitution<> envSubst = toSubst(env);
        json::value guard = convert_data_expression(data::replace_variables(cond.condition(), envSubst), beta);
        json::object negGuard = negateGuardExpression(guard);
        for (auto& [edge, target] : reSource(successors(makeLoc(cond.then_case(), beta, env), unfolding, pending), locationName(loc))) {
          strengthenGuardOfEdge(edge, guard);
          result.push_back({edge, target});
        }
        for (auto& [edge, target] : reSource(successors(makeLoc(cond.else_case(), beta, env), unfolding, pending), locationName(loc))) {
          strengthenGuardOfEdge(edge, negGuard);
          result.push_back({edge, target});
        }
      }
      // (Inst+Fijación)  P(actual): the transitions are those of the body explored as
      // the first-class location (body, mergedβ, env'), which is NOT committed to the
      // automaton — it lives only in this recursion. enterInstance composes the
      // substitution into env' (for the body's guards) and accumulates the parameter
      // assignments onto pending (emitted on the next action edge). The body's tail
      // instances stay symbolic, so tail recursion is finite.
      else if (is_process_instance(expr)) {
        const process_instance& procInst = atermpp::down_cast<process_instance>(expr);
        const process_identifier& id = procInst.identifier();
        if (unfolding.contains(id)) {
          throw jani_translation_error("Unguarded recursion through process " + pp(id) +
            " (no action before recursing); cannot build a finite automaton.");
        }
        unfolding.insert(id);

        const process_equation& eqn = lookup_process_equation(id);
        instance_entry e = enterInstance(id, eqn, procInst.actual_parameters(), beta, env, pending);
        for (auto& [edge, target] :
             reSource(successors(makeLoc(eqn.expression(), e.mergedBeta, e.newEnv), unfolding, e.newPending),
                      locationName(loc))) {
          result.push_back({edge, target});
        }
      }
      else {
        throw jani_translation_error(
          "Expression " + pp(expr) + " not supported as a location in the automaton.");
      }

      return result;
    }

    // Records the JANI variables named by a location's symbol map, for declaration.
    void collectVariables(const abstract_location& loc) {
      if (std::holds_alternative<termination_t>(loc)) {
        return;
      }
      for (const auto& [var, name] : std::get<process_location>(loc).beta) {
        jani_variable_sorts[name] = var.sort();
      }
    }

    // Explores the locations reachable from `initial` and commits the
    // corresponding JANI locations and edges to the automaton. successors is pure,
    // so this is the only place where the automaton is mutated. Termination and
    // delta locations fall out naturally as discovered locations with no outgoing
    // edges. Returns the name of the initial location.
    string translateProcessExpression(const abstract_location& initial) {
      list<abstract_location> work_queue = {initial};
      set<abstract_location> discovered = {initial};

      collectVariables(initial);
      addStateToAutomaton(json::object{{"name", locationName(initial)}});

      while (!work_queue.empty()) {
        abstract_location s = work_queue.front();
        work_queue.pop_front();

        for (auto& [edge, target] : successors(s)) {
          addEdgeToAutomaton(edge);
          if (!discovered.contains(target)) {
            discovered.insert(target);
            collectVariables(target);
            addStateToAutomaton(json::object{{"name", locationName(target)}});
            work_queue.push_back(target);
          }
        }
      }

      return locationName(initial);
    }

    json::object translate(){

      auto initialLocation = translateProcessExpression(makeLoc(initial_process_call, symbol_map{}));

      jani_automaton["initial-locations"] = json::array({initialLocation});

      // Declare the automaton-local variables discovered during exploration. Their
      // values are established by the outgoing-edge assignments of the instance
      // nodes, so a default initial-value suffices.
      json::array variables;
      for (const auto& [name, sort] : jani_variable_sorts) {
        variables.push_back(json::object{
          {"name", name},
          {"type", convert_sort_expression(sort)},
          {"initial-value", initial_value_for_sort(sort)}
        });
      }
      jani_automaton["variables"] = variables;

      // No unreachable-cleanup pass needed: successors is pure and
      // translateProcessExpression only commits reachable locations/edges.

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
  void checkSyncs(actionSet readingActions) {
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
  actionSet readingActions;
  actionSet writingActions;
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

    pcrl_to_automaton_translator translator(spec, procInst, automatonName);
    auto automaton = translator.translate();
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
        {"type", "mdp"},
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
            auto assignment = destination.at("assignments").at(i).as_object();
            string oldRef = assignment.at("ref").as_string().c_str();

            // Transient action-data assignments are tagged by a digit-leading ref
            // (the action argument index); these are replicated to every reading
            // action that may read this writing action's value. Assignments with a
            // non-digit ref (e.g. recursion parameters P_n) are not part of the
            // communication machinery and must be preserved untouched.
            if (!isdigit(oldRef[0])) {
              newAssignments.push_back(assignment);
              continue;
            }

            json::value val = assignment.at("value");
            for (auto& readAction : writeToReads[actionName]) {
              json::object newAssignment = assignment;
              newAssignment["ref"] = readAction + "_" + oldRef;
              newAssignment["value"] = val;
              newAssignments.push_back(newAssignment);
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
