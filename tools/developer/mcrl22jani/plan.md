# Translation psedocode iteration

In this file we'll iterate on the high-level algorithmics to 
generate JANI from mcrl2. First we'll focus on ACP operators. Then
on pCRL, adding data and operators that use data, i.e, process instances,
choice quantification and conditionals. Finally, we'll add the dist operator
which will require us to modify the "compute transitions" logic, but not the
graph exploration logic.

## ACP operators translation

Given we have 

p :== a | delta | p . q | p + q | P

how do we translate this?
we need to treat this as a graph traversal, not an AST traversal.
This is because of recursion, posible thanks to the production P. So we need to only explore the outgoing
trasitions of a location when we visit it.

A location up to this point is identified by a process expression. This will change once we include data

So, having a starting location, we'll put it in a queue and then loop until this queue is empty.

On each iteration we should:
- compute outgoing transitions and add successor locations to our queue
- remove the location we've just visited
- add the location we just visited to a "discovered locations", so that queueing it again
  will not make us compute its transitions again.
- loop back

For now the compute transitions routine should just match the process
expression type and add the successor locations and transitions to them
and make them available somehow so they can be added to the queue.

## Data without communication(no summation)

Now we add the possiblity to have data along with locations

p :== a(d_1, .., d_n) | delta | p . q | p + q | P(d_1, ..., d_n) | c -> p <> q

Now we'll have to change how we identify a location.

Previously, a location was identified with a process expression. Now this is not the case.
We may have the same process expression `a(n)`, but have that expression under a different context
regarding what `n` means. If we have equations `P(n : Nat) = a(n)` and `Q(n : Nat) = a(n)`, then 
free variable `n` is not handled with the same JANI variable in both cases, but using a prefixed variable
in each case, `P_n` and `Q_n` respectively. So we need to have an symbol map included in what we use to 
identify a location.

Also, we now have the **process instance** construct, which means that we'll have the notion of setting a 
variable to a fixed value. A location like this will then need to copy all transitions from its body, but including assignments to the variables to be set and also rewriting conditions with these assignments as rewrite rules. 

In synthesis, we'll need to define update the abstract_location type for it to be a three-tuple 
`(process_expression, map<data_variable, string /*jani variable*/>, map<data_variable, data_expression)`

this three-tuple corresponds to three things:
- a process expression
- an symbol map for its free variables
- a subsitution environment for its free variables

After this change, we'll need to update the way we handle locations in various parts of the code.

Then, we'll need to add cases for the new constructs in `successors` and use new
rewriting logic using mcrl2 rewriters.

## Summation

we now consider the summation operator, which introduces new variables that we interpret as incoming messages
from another, parallel running process.

To this end, we will run a pass over the whole AST to separate action labels as either reading or writing,
populating respective sets. Then we will perform the automata generation with this knowledge, adding 
assignments to edges in order to either read or write, depending on the type of action, as per the 
operational semantics rules.

## Probabilistic choice