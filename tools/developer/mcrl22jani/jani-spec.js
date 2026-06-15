
// Identifiers
var Identifier = /[^#].*/; // alternative (with XRegExp) to forbid line breaks, right-to-left embedding etc.:
                           // /[^#\p{Cc}\p{Cf}\p{Co}\p{Cn}\p{zL}\p{Zp}][^\p{Cc}\p{Cf}\p{Co}\p{Cn}\p{zL}\p{Zp}]*/

// Types
// We cover only the most basic types at the moment.
// In the remainder of the specification, all requirements like "y must be of type x" are to be interpreted
// as "type x must be assignable from y's type".
var BasicType = schema([
  "bool", // assignable from bool
  "int", // numeric; assignable from int and bounded int
  "real" // numeric; assignable from all numeric types
]);
var BoundedType = schema({ // numeric if base is numeric; lower-bound or upper-bound or both must be present;
                           // assignable from those types that base is assignable from
  "kind": "bounded",
  "base": [ "int", "real" ],
  "?lower-bound": Expression, // smallest value allowed by the type; constant expression of the base type
  "?upper-bound": Expression // largest value allowed by the type; constant expression of the base type
});
var Type = schema([
  BasicType,
  BoundedType,
  "clock", // numeric; only allowed for TA, PTA, STA, HA, PHA and SHA; assignable from int and bounded int
  "continuous" // numeric; continuous variable that changes over time as allowed by the current location's
               // invariant; only allowed for HA, PHA and SHA; assignable from all numeric types
]);

// Expressions
var ConstantValue = schema([
  Number, // numeric value; has type int if it is an integer and type real otherwise
  true, false, // Boolean value; has type bool
  { // mathematical constants that cannot be expressed using numeric values and basic jani-model expressions
    "constant": [
      "e", // Euler's number (the base of the natural logarithm); type real
      "π" // π (the ratio of a circle's circumference to its diameter); type real
    ]
  }
]);
var Expression = schema([ // an expression is constant if all subexpressions are constant, unless noted otherwise
  ConstantValue, // constant value
  Identifier, // constant or variable reference; has the type of the constant or variable; if this type is a bounded
              // type with base type t, then it has type t instead; constant expression iff it is a constant
              // reference
  { // if-then-else: computes if if then then else else
    "op": "ite", // the result type is the type of then if that is assignable from the type of else, or the type of
                 // else if that is assignable from the type of then (previously: the result type is the most
                 // specific type assignable from the types of then and else)
    "if": schema.self, // the condition; type bool
    "then": schema.self, // the consequence
    "else": schema.self // the alternative
  },
  { // disjunction / conjunction: computes left ∨ right / left ∧ right
    "op": [ "∨", "∧" ], // result type is bool
    "left": schema.self, // the left operand; type bool
    "right": schema.self // the right operand; type bool
  },
  { // negation: computes ¬exp
    "op": "¬", // result type is bool
    "exp": schema.self // the single operand; type bool
  },
  { // equality comparison: computes left = right / left ≠ right
    "op": [ "=", "≠" ], // result type is bool; left and right must be assignable to some common type
    "left": schema.self, // the left operand
    "right": schema.self // the right operand
  },
  { // numeric comparison: computes left < right / left ≤ right
    "op": [ "<", "≤" ], // result type is bool
    "left": schema.self, // the left operand; numeric type
    "right": schema.self // the right operand; numeric type
  },
  { // addition / subtraction / multiplication / modulo:
    // computes left + right / left - right / left * right / left modulo right
    "op": [ "+", "-", "*", "%" ], // result type is int (if left and right are both assignable to int) or real
                                  // (otherwise)
    "left": schema.self, // the left operand; numeric type (must be int if op is "%")
    "right": schema.self // the right operand; numeric type (must be int if op is "%")
  },
  { // division / exponentiation / logarithm:
    // computes left/right / leftright / logright(left)
    "op": [ "/", "pow", "log" ], // result type is real (division is real division, no truncation for integers)
    "left": schema.self, // the left operand; numeric type
    "right": schema.self // the right operand; numeric type
  },
  { // floor / ceiling: computes ⌊exp⌋ / ⌈exp⌉
    "op": [ "floor", "ceil" ], // result type is int
    "exp": schema.self // the single operand; numeric type
  },
  { // derivative: refers to the first derivative of x; only allowed in HA, PHA and SHA; not a constant expression
    "op": "der", // result type is real
    "var": Identifier // the name of a continuous global variable; if the expression occurs within an automaton,
                      // it can also be the name of a continuous local variable of that automaton
  },
  DistributionSampling // only allowed for STA and SHA; defined in the Stochastic Timed Automata section;
                       // an expression in which this alternative does not occur is called sampling-free;
                       // not a constant expression
]);

// L-values (for assignment left-hand sides)
var LValue = schema([
  Identifier // the variable to assign to
]);


Automata Composition

// Automata composition
var Composition = schema({
  "elements": Array.of({
    "automaton": Identifier, // the name of an automaton
    "?input-enable": Array.of(Identifier), // a set of action names on which to make the automaton input-enabled;
                                           // for CTMC and CTMDP, the new transitions have rate 1
    "?comment": String // an optional comment
  }),
  "?syncs": Array.of({
    "synchronise": Array.of([ Identifier, null ]), // a list of action names or null, same length as elements
    "?result": Identifier, // an action name, the result of the synchronisation; if omitted, it is the silent action
    "?comment": String, // an optional comment
  }),
  "?comment": String // an optional comment
});

Models and Automata

var Metadata = schema({
  "?version": String, // information about the version of this model (e.g. the date when it was last modified)
  "?author": String, // information about the creator of the model
  "?description": String, // a description of the model
  "?doi": String, // the DOI of the paper where this model was introduced/used/described 
  "?url": String, // a URL pointing to more information about the model
});

var ModelType = schema([
  "lts", // LTS: a labelled transition system (or Kripke structure or finite state automaton) (untimed)
  "dtmc", // DTMC: a discrete-time Markov chain (untimed)
  "ctmc", // CTMC: a continuous-time Markov chain (timed)
  "mdp", // MDP: a discrete-time Markov decision process (untimed)
  "ctmdp", // CTMDP: a continuous-time Markov decision process (timed)
  "ma", // MA: a Markov automaton (timed)
  "ta", // TA: a timed automaton (timed)
  "pta", // PTA: a probabilistic timed automaton (timed)
  "sta", // STA: a stochastic timed automaton (timed)
  "ha", // HA: a hybrid automaton (timed)
  "pha", // PHA: a probabilistic hybrid automaton (timed)
  "sha" // SHA: a stochastic hybrid automaton (timed)
]);

var ModelFeature = schema([ // names starting with "x-" will not be defined and are available for internal use
  "arrays", // support for array types, defined in the Extensions section
  "cvar-properties", // support for conditional value at risk properties, defined in the Extensions section
  "datatypes", // support for complex datatypes, defined in the Extensions section
  "derived-operators", // support for some derived operators in expressions, defined in the Extensions section
  "edge-priorities", // support for priorities on edges, defined in the Extensions section
  "functions", // support for functions, defined in the Extensions section
  "hyperbolic-functions", // support for hyperbolic functions, defined in the Extensions section
  "named-expressions", // support for named subexpressions, defined in the Extensions section
  "nondet-selection", // support for nondeterministic selection in expressions, defined in the Extensions section
  "quantile-properties", // support for quantile properties, defined in the Extensions section
  "state-exit-rewards", // support for accumulating rewards when leaving a state, defined in the Extensions section
  "tradeoff-properties", // support for multi-objective tradeoff properties, defined in the Extensions section
  "trigonometric-functions" // support for trigonometric functions, defined in the Extensions section
]);

var VariableDeclaration = schema({
  "name": Identifier, // the variable's name, unique among all constants and global variables
                      // as well as among local variables if the variable is declared within an automaton
  "type": Type, // the variable's type; must not be or contain "clock" or "continuous" if transient is true
  "?transient": [ true, false ], // transient variable if present and true; a transient variable behaves as follows:
                                 // (a) when in a state, its value is that of the expression specified in
                                 //     "transient-values" for the locations corresponding to that state, or its
                                 //     initial value if no expression is specified in any of the locations
                                 //     (and if multiple expressions are specified, that is a modelling error);
                                 // (b) when taking a transition, its value is set to its initial value, then all
                                 //     assignments of the edges corresponding to the transition are executed.
  "?initial-value": [ // if omitted: any value allowed by type (possibly restricted by the restrict-initial
                      // attributes of the model or an automaton); must be present if transient is present and true
    Expression // a constant expression of type type
  ],
  "?comment": String // an optional comment
});

var ConstantDeclaration = schema({
  "name": Identifier, // the constant's name, unique among all constants and variables
  "type": [ BasicType, BoundedType ], // the constant's type; bounded types must not refer to this constant or
                                      // constants declared after this one in the corresponding array
  "?value": Expression, // the constant's value, of type type; constant expression that must not refer to this
                        // constant or constants declared after this one in the corresponding array;
                        // if omitted, the constant is a model parameter
  "?comment": String // an optional comment
});

var Model = schema({
  "jani-version": Number.min(1).step(1), // the jani-model version of this model
  "name": String, // the name of the model (e.g. the name of the underlying model file)
  "?metadata": Metadata,
  "type": ModelType, // the model's type
  "?features": Array.of(ModelFeature), // extended jani-model features defined elsewhere that are used by this model
  "?actions": Array.of({ // the model's actions
    "name": Identifier, // the action's name, unique among all actions
    "?comment": String // an optional comment
  }),
  "?constants": Array.of(ConstantDeclaration), // the model's constants
  "?variables": Array.of(VariableDeclaration), // the model's global variables
  "?restrict-initial": { // restricts the initial values of the global variables
    "exp": Expression, // the initial states expression, type bool, must not reference transient variables
    "?comment": String // an optional comment
  },
  "?properties": Array.of(Property), // the properties to check
  "automata": Array.of(Automaton), // the model's automata; at least one
  "system": Composition // the model's automata network composition expression, note that one automaton 
                        // can appear multiple times (= in multiple instances)
});

var Automaton = schema({ // all expressions and assignments inside an automaton can only reference its own local
                         // variables and the global variables of the enclosing model
  "name": Identifier, // the name of the automaton, unique among all automata
  "?variables": Array.of(VariableDeclaration), // the local variables of the automaton
  "?restrict-initial": { // restricts the initial values of the local variables of this automaton (i.e. it has no
                         // effect on the initial values of global variables or local variables of other automata)
    "exp": Expression, // the initial states expression; type bool, must not reference transient variables
    "?comment": String // an optional comment
  },
  "locations": Array.of({ // the locations that make up the automaton; at least one
    "name": Identifier, // the name of the location, unique among all locations of this automaton
    "?time-progress": { // the location's time progress condition, not allowed except TA, PTA, STA, HA, PHA and STA,
                        // type bool; if omitted in TA, PTA, STA, HA, PHA or SHA, it is true
      "exp": Expression, // the invariant expression, type bool
      "?comment": String // an optional comment
    },
    "?transient-values": Array.of({ // values for transient variables in this location
      "ref": LValue, // what to set the value for
      "value": Expression, // the value, must not contain references to transient variables or variables of type
                           // "clock" or "continuous"
      "?comment": String // an optional comment
    }),
    "?comment": String // an optional comment
  }),
  "initial-locations": Array.of(Identifier), // the automaton's initial locations
  "edges": Array.of({ // the edges connecting the locations
    "location": Identifier, // the edge's source location
    "?action": Identifier, // the edge's action label; if omitted, the label is the silent action
    "?rate": { // the edge's rate, required for CTMC and CTMDP, optional for MA,
               // optional in DTMC where it represents the weight of the edge to be able to resolve nondeterminism, 
               // not allowed in all other model types; if present in a MA, action must be omitted
      "exp": Expression, // the rate expression, type real
      "?comment": String // an optional comment
    },
    "?guard": { // the edge's guard; if omitted, it is true
      "exp": Expression, // the guard expression, type bool
      "?comment": String // an optional comment
    },
    "destinations": Array.of({ // the destinations of the edge, at least one, at most one for LTS, TA and HA
      "location": Identifier, // the destination's target location
      "?probability": { // the destination's probability, not allowed in LTS, TA and HA; if omitted, it is 1
        "exp": Expression, // the probability expression, type real; note that this may evaluate to zero
        "?comment": String // an optional comment
      },
      "?assignments": Array.of({ // the set of assignments to execute atomically
        "ref": LValue, // what to assign to (can be both transient and non-transient)
        "value": Expression, // the new value to assign to the variable; must be of the variable's type;
                             // if the variable's type is clock, must be a clock- and sampling-free expression
        "?index": Number.step(1), // the index, to create sequences of atomic assignment sets, default 0
        "?comment": String // an optional comment
      }),
      "?comment": String // an optional comment
    }),
    "?comment": String // an optional comment
  }),
  "?comment": String // an optional comment
});


Properties

var Property = schema({
  "name": Identifier, // the property's name, unique among all the properties of the model
  "expression": PropertyExpression, // the state-set formula
  "?comment": String // an optional comment
});
var PropertyInterval = schema({
  "?lower": Expression, // constant expression, must be present if upper is omitted
  "?lower-exclusive": [ true, false ], // indicates whether the lower bound is exclusive (else inclusive);
                                       // must not be present if lower is not present;
                                       // if not present when lower is present, the value is false
  "?upper": Expression,  // constant expression, must be present if lower is omitted
  "?upper-exclusive": [ true, false ] // indicates whether the upper bound is exclusive (else inclusive);
                                      // must not be present if upper is not present;
                                      // if not present when upper is present, the value is false
});
var RewardAccumulation = schema(Array.of([ // defines when to accumulate the value of a reward; should not contain
                                           // any entry more than once, and must contain at least one entry:
  "steps", // evaluate the expression when taking a transition, after* all assignments have been executed,
           // and accumulate the result (* note that this is different from PRISM's transition rewards)
  "time" // evaluate the expression when delaying in a state and accumulate the result times the delay
         // (zero in untimed models)
]));
var PropertyExpression = schema([
  [...], // all the definitions of the Expression schema
  { // filters the values of sets of reachable states ("filter" in PRISM)
    "op": "filter",
    "fun": [
      "min", "max", "sum", "avg", // values must have type real and states must characterise a non-empty set
                                  // of states; result type is real
      "count", // values must have type bool, result type is int
      "∀", "∃", // values must have type bool, result type is bool
      "argmin", "argmax", // values must have type real, result type is set of states
      "values" // values must have type real or bool, result type is set of reals or bools ("printall" in PRISM)
               // the result type is a set of values of the type of values ("printall" in PRISM)
    ],
    "values": schema.self, // the formula that produces the values to apply fun to
    "states": schema.self // the formula characterising the relevant subset of the reachable states; type bool
  },
  // All of the operators below must not occur outside of a filter expression
  // to avoid any ambiguity for models with multiple initial states
  { // maximum/minimum probability ("P" operator in PRISM)
    "op": [ "Pmin", "Pmax" ], // result type is real
    "exp": schema.self, // the path formula, type bool
  },
  { // for all paths / there exists a path ("A" and "E" operators in PRISM)
    "op": [ "∀", "∃" ], // result type is bool
    "exp": schema.self, // the path formula, type bool
  },
  { // maximum/minimum expected (accumulated) value ("F", "C<=", "C" or "I" reward property in PRISM)
    "op": [ "Emin", "Emax" ], // result type is real
    "exp": Expression, // the value expression; numeric type
    "?accumulate": RewardAccumulation, // whether and when to accumulate exp's value
                                       // (accumulate to obtain an "F", "C<=" or "C" property)
    "?reach": schema.self, // the reachability state formula (for PRISM "I" and "F"-style properties), type bool
    "?step-instant": Expression, // or step instant (number of edges taken, for "I" and "C<=" properties), type int
    "?time-instant": Expression, // or time instant, only allowed in timed models (for "I" and "C<="), type real
    "?reward-instants": Array.of({ // or a disjunction of reward instants
      "exp": Expression, // what to accumulate over steps and time for this subformula
      "accumulate": RewardAccumulation, // must not be empty
      "instant": Expression // the instant; constant expression (also applies to step- and time-instant)
    })
  },
  { // maximum/minimum long-run average value ("S" operator or reward property in PRISM)
    "op": [ "Smin", "Smax" ], // result type is real
    "exp": schema.self, // the value expression or state formula; bool (if state formula) or numeric type (if value);
                        // interpret Booleans as true = 1, false = 0 to compute the steady-state probability
    "?accumulate": RewardAccumulation // when to incur exp's value; must not be empty; if absent, it is [ "steps",
                                      // "time" ] for timed models, and [ "exit", "steps" ] for untimed models
  },
  { // until / weak until
    "op": [ "U", "W" ], // result type is bool
    "left": schema.self, // the left formula, type bool
    "right": schema.self, // the right formula, type bool
    "?step-bounds": PropertyInterval, // step bounds (number of edges taken) of type int
    "?time-bounds": PropertyInterval, // and time bounds of numeric type, only allowed in timed models
    "?reward-bounds": Array.of({ // and a conjunction of reward bounds
      "exp": Expression, // what to accumulate over steps and time for this subformula
      "accumulate": RewardAccumulation, // must not be empty
      "bounds": PropertyInterval // the bounds of numeric type
    })
  },
  { // state predicates
    "op": [ "initial", "deadlock", "timelock" ] // result type is bool,
  }                                             // "timelock" is only allowed in TA, PTA, STA, HA, PHA, SHA
]);


Stochastic Timed Automata

var DistributionSampling = schema({
  "distribution": [
    "DiscreteUniform",      // Discrete uniform distribution:
                            // 2 int args a (inclusive lower bound) and b (inclusive upper bound),
                            // requires a ≤ b, result type is int,
                            // pmf f(k) = 1/(b - a + 1) for k = a, a+1, ..., b
    "Bernoulli",            // Bernoulli distribution:
                            // 1 real arg p (probability of success),
                            // requires 0 ≤ p ≤ 1, result type is int,
                            // pmf f(0) = 1 - p and f(1) = p
    "Binomial",             // Binomial distribution:
                            // 1 real arg p (probability of a success) and 1 int arg n (number of trials),
                            // requires 0 ≤ p ≤ 1 and n ≥ 0, result type is int,
                            // pmf f(k) = (n choose k) * p^k * (1 - p)^(n - k) for k = 0, 1, ..., n
    "NegativeBinomial",     // Negative binomial distribution:
                            // 2 real args p (probability of a success) and r (number of failures before stop),
                            // requires 0 ≤ p ≤ 1 and r ≥ 0, result type is int,
                            // pmf f(k) = ((k + r - 1) choose k) * p^k * (1 - p)^r for k = 0, 1, ...
    "Poisson",              // Poisson distribution:
                            // 1 real arg λ (the rate),
                            // requires λ > 0, result type is int,
                            // pmf f(k) = (λ^k / k!) * e^(-λ) for k = 0, 1, 2, ...
    "Geometric",            // Geometric distribution:
                            // 1 real arg p (probability of a success),
                            // requires 0 ≤ p ≤ 1, result type is int,
                            // pmf f(k) = p * (1 - p)^(k - 1) for k = 1, 2, ...
    "Hypergeometric",       // Hypergeometric distribution:
                            // 3 int args N (population size), K (#successes in population) and N (#draws),
                            // requires N ≥ 0, 0 ≤ K ≤ N and 0 ≤ n ≤ N, result type is int,
                            // pmf f(k) = (K choose k) * ((N - K) choose (n - k)) / (N choose n)
                            //     for k ∈ { max(0, n + K - N), ..., min(n, K) }
    "ConwayMaxwellPoisson", // Conway-Maxwell-Poisson distribution:
                            // 2 real args λ (the rate) and ν (the rate of decay),
                            // requires λ > 0 and ν ≥ 0, result type is int,
                            // pmf f(k) = (λ^x / (x!^ν)) * (1 / (Z(λ, ν))) for k = 0, 1, 2, ...
    "Zipf",                 // Zipf distribution:
                            // 1 real arg s (value of the exponent) and 1 int arg N (number of elements),
                            // requires s > 0 and N ≥ 1, result type is int,
                            // pmf f(k) = (1 / k^s) / H_{N, s} for k = 1, 2, ..., N
    "Uniform",              // Continuous uniform distribution:
                            // 2 real args a (inclusive lower bound) and b (inclusive upper bound),
                            // requires a ≤ b, result type is real,
                            // see https://en.wikipedia.org/wiki/Uniform_distribution_%28continuous%29
    "Normal",               // Normal distribution:
                            // 2 real args µ (mean) and σ (standard deviation),
                            // requires σ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Normal_distribution
    "FoldedNormal",         // Folded normal distribution:
                            // 2 real args µ (mean of the underlying normal distribution) and σ (standard deviation
                            // of the underlying normal distribution),
                            // requires σ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Folded_normal_distribution
    "LogNormal",            // Log-normal distribution:
                            // 2 real args μ (log-scale) and σ (shape),
                            // requires σ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Log-normal_distribution
    "Beta",                 // Beta distribution:
                            // 2 real args α and β (shape parameters),
                            // requires α ≥ 0 and β ≥ 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Beta_distribution
    "Cauchy",               // Cauchy distribution:
                            // 2 real args x0 (location) and γ (scale),
                            // requires γ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Cauchy_distribution
    "Chi",                  // Chi distribution:
                            // 1 int arg k (degrees of freedom),
                            // requires k > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Chi_distribution
    "ChiSquared",           // Chi² distribution:
                            // 1 int arg k (degrees of freedom),
                            // requires k > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Chi-squared_distribution
    "Erlang",               // Erlang distribution:
                            // 1 int arg k (the shape) and 1 real arg λ (the rate),
                            // requires k ≥ 0 and λ ≥ 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Erlang_distribution
    "Exponential",          // Exponential distribution:
                            // 1 real arg λ (the rate),
                            // requires λ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Exponential_distribution
    "FisherSnedecor",       // Fisher-Snedecor distribution:
                            // 2 real args d1 and d2 (first and second degree of freedom),
                            // requires d1 > 0 and d2 > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/F-distribution
    "Gamma",                // Gamma distribution:
                            // 2 real args α (the shape) and β (the rate),
                            // requires α > 0 and β > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Gamma_distribution
    "InverseGamma",         // Inverse gamma distribution:
                            // 2 real args α (the shape) and β (the scale),
                            // requires α > 0 and β > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Inverse-gamma_distribution
    "Laplace",              // Laplace distribution:
                            // 2 real args µ (the location) and b (the scale),
                            // requires b > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Laplace_distribution
    "Pareto",               // Pareto distribution:
                            // 2 real args xm (the scale) and α (the shape),
                            // requires xm > 0 and α > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Pareto_distribution
    "Rayleigh",             // Rayleigh distribution:
                            // 1 real arg σ (the scale),
                            // requires σ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Rayleigh_distribution
    "Stable",               // Stable distribution:
                            // 4 real args α (stability), β (skewness), c (scale) and µ (location),
                            // requires 2 ≥ α > 0, 1 ≥ β ≥ -1 and c > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Stable_distribution
    "StudentT",             // Student's t-distribution:
                            // 3 real args µ (location), σ (scale) and ν (degrees of freedom),
                            // requires σ > 0 and ν > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Student's_t-distribution
    "Weibull",              // Weibull distribution:
                            // 2 real args k (the shape) and λ (the scale),
                            // requires k > 0 and λ > 0, result type is real,
                            // see https://en.wikipedia.org/wiki/Weibull_distribution
    "Triangular"            // Triangular distribution:
                            // 3 real args a (lower bound), b (upper bound) and c (mode),
                            // requires a ≤ c ≤ b, result type is real,
                            // see https://en.wikipedia.org/wiki/Triangular_distribution
  ],
  "args": Array.of(Expression) // elements must not contain distribution sampling
});


Extensions

This section specifies all official extended jani-model features.
The following schemas are used by several extensions as noted within the specification of the extension:

// Specifies a reward (accumulated or instantaneous), i.e. a random variable over paths:
var RewardSpec = schema({
  "exp": Expression, // the reward value expression; numeric type
  "?accumulate": RewardAccumulation, // whether and when to accumulate exp's value
  "?reach": schema.self, // the reachability state formula, type bool
  "?step-bounds": PropertyInterval, // and step bounds (number of edges taken) of type int
  "?time-bounds": PropertyInterval, // and time bounds of numeric type, only allowed in timed models
  "?reward-bounds": Array.of({ // and a conjunction of reward bounds
    "exp": Expression, // what to accumulate over steps and time for this subformula
    "accumulate": RewardAccumulation, // must not be empty
    "bounds": PropertyInterval // the bounds of numeric type
  })
});

arrays

// Adds the following alternative to the Type schema:
var Type = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // array type; assignable from type t if t is an array type and base is assignable from t's base (matching
    // length in assignments needs to be checked at runtime)
    "kind": "array",
    "base": schema.self // the type of the elements of the array
  }
]);

// Adds the following alternatives to the Expression schema:
var Expression = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // array access: returns the value at index index in the array value exp 
    "op": "aa",
    "exp": schema.self, // of array type
    "index": schema.self // type int
  },
  { // array value: returns an array with the specified element values
    "op": "av",
    "elements": Array.of(schema.self) // at least one element; must all be assignable to some common type
  },
  { // array constructor: returns an array of length length constructed by instantiating exp for each index
    "op": "ac",
    "var": Identifier, // the name of the free variable of type int used in exp as the element index;
                       // must be unique among global variables and constants; if the expression occurs within
                       // an automaton, it must also be unique among that automaton's local variables
    "length": schema.self, // type int
    "exp": schema.self // must all be assignable to some common type; may reference var
  }
]);

// Adds the following alternative to the LValue schema:
var LValue = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // the storage location at index index in the array value exp
    "op": "aa",
    "exp": schema.self, // of array type
    "index": Expression // type int
  }
]);

cvar-properties

Uses the RewardSpec schema.

// Adds the following alternative to the PropertyExpression schema:
var PropertyExpression = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // maximum/minimum conditional value at risk of reward values
    "op": [ "CVaRmin", "CVaRmax" ], // result type is real
    "quantile": Expression, // the quantile expression, constant expression of numeric type
    "direction": [ "<", ">" ], // the direction to compute the expected value for: below or above the quantile
    "reward": RewardSpec // the reward values
  }
]);

datatypes

// Adds the following schema:
var DatatypeDefinition = schema({ // datatype definition
  "name": Identifier, // the unique name of the datatype
  "members": Array.of({
    "name": Identifier, // the name of the member, unique for this datatype
    "type": Type // the type of the member; can be another datatype (order of datatype definitions does not matter);
                 // must not be or contain clock or continuous
  })
});

// Adds the following attribute to the Model schema:
var Model = schema({
  [...], // all the definitions of basic jani-model and other active extensions
  "?datatypes": Array.of(DatatypeDefinition)
});

// Adds the following alternatives to the Type schema:
var Type = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // datatype; assignable only from the same datatype (i.e. the same ref)
    "kind": "datatype",
    "ref": Identifier // the name of the datatype
  },
  { // option type; assignable from type t if t is empty option or if base is assignable from t or if t is
    // an option type and base is assignable from t's base
    "kind": "option",
    "base": schema.self // the element type; must not be or contain "clock" or "continuous"
  }
]);

// Adds the following alternatives to the Expression schema:
var Expression = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // datatype member access: returns the value of member member of the datatype value exp
    "op": "da",
    "exp": schema.self, // of datatype type
    "member": Identifier // the name of the member to access, must be a member of the type of exp
  },
  { // datatype value: returns a value of the specified datatype with the specified member values
    "op": "dv",
    "type": Identifier, // the name of a datatype
    "values": Array.of({ // must have exactly one element for each member of the datatype
      "member": Identifier, // the name of the member
      "value": schema.self // the value, must be of the type of the member
    }
  },
  { // option value access: returns the value stored in the option if it is not the empty option, otherwise it is a
    // runtime error
    "op": "oa",
    "exp": schema.self // of option type
  },
  { // option value: returns an option that stores the specified value
    "op": "ov",
    "exp": schema.self // the value; must not be the empty option
  },
  { // empty option: returns the empty option, which has type empty option that is assignable from itself only
    "op": "empty"
  }
]);

// Adds the following alternative to the LValue schema:
var LValue = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // the storage location of member member in the datatype value exp
    "op": "da",
    "exp": schema.self, // of datatype type
    "member": Identifier // the name of a member of the datatype
  },
  { // the storage location for the value in a non-empty option
    "op": "oa",
    "exp": schema.self // of option type
  }
]);

derived-operators

// Adds the following alternatives to the Expression schema:
var Expression = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // implication: computes left ⇒ right
    "op": [ "⇒" ], // result type is bool
    "left": schema.self, // the left operand; type bool
    "right": schema.self // the right operand; type bool
  },
  { // numeric comparison: computes left > right / left ≥ right
    // in basic jani-model, this can be expressed as "right < left" / "right ≤ left"
    "op": [ ">", "≥" ], // result type is bool
    "left": schema.self, // the left operand; numeric type
    "right": schema.self // the right operand; numeric type
  },
  { // maximum / minimum: computes max(left, right) / min(left, right)
    // in basic jani-model, this can be expressed as "if left < right then right else left" (or with > for min)
    "op": [ "min", "max" ], // result type is int (if left and right are int) or real (otherwise)
    "left": schema.self, // the left operand; numeric type
    "right": schema.self // the right operand; numeric type
  },
  { // absolute value / sign / truncation: computes abs(exp) / sgn(exp) / (int)exp
    // in basic jani-model, these can be expressed with if-then-else and comparisons (and ceil/floor for truncation)
    "op": [ "abs", "sgn", "trc" ], // result type is int (if op is "sgn" or "trc", or if op is "abs" and exp is int)
                                   // or real (otherwise)
    "exp": schema.self // the single operand; numeric type
  },
]);

// Adds the following alternatives to the PropertyExpression schema:
var PropertyExpression = schema([
  [...], // all the definitions of basic jani-model and other active extensions
  { // eventually / always
    "op": [ "F", "G" ], // result type is bool
    "exp": schema.self, // the single operand, type bool
    "?step-bounds": PropertyInterval, // step bounds (number of edges taken) of type int
    "?time-bounds": PropertyInterval, // and time bounds of numeric type, only allowed in timed models
    "?reward-bounds": Array.of({ // and a conjunction of reward bounds
      "exp": Expression, // what to accumulate over steps and time for this subformula
      "accumulate": RewardAccumulation, // must not be empty
      "bounds": PropertyInterval // the bounds of numeric type
    })
  },
  { // release
    "op": [ "R" ], // result type is bool
    "left": schema.self, // the left formula, type bool
    "right": schema.self, // the right formula, type bool
    "?step-bounds": PropertyInterval, // step bounds (number of edges taken) of type int
    "?time-bounds": PropertyInterval, // and time bounds of numeric type, only allowed in timed models
    "?reward-bounds": Array.of({ // and a conjunction of reward bounds
      "exp": Expression, // what to accumulate over steps and time for this subformula
      "accumulate": RewardAccumulation, // must not be empty
      "bounds": PropertyInterval // the bounds of numeric type
    })
  }
]);




