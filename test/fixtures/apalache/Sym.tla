---- MODULE Sym ----
EXTENDS Integers
CONSTANT
  \* @type: Set(NODE);
  Nodes
VARIABLE
  \* @type: Set(<<NODE, NODE>>);
  edge
ConstInit == Nodes = {"a_OF_NODE", "b_OF_NODE", "c_OF_NODE"}
Init == edge \in SUBSET (Nodes \X Nodes)
Next == UNCHANGED edge
\* antisymmetry: false for some graphs
Anti == \A x, y \in Nodes: (<<x, y>> \in edge /\ <<y, x>> \in edge) => x = y
\* true of every graph
Closed == \A x, y \in Nodes: <<x, y>> \in edge => (x \in Nodes /\ y \in Nodes)
====
