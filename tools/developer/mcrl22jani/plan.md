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
