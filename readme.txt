NEW VERSION OF SOFTWARE

Several important changes have been made to create a layered structure for the
new version of the software. The most important changes are summarized below.

*** FIRST CHANGE ***
A total refactoring has been made, now the software is based on an actual stack
of layers, each component in a layer relies on the services from the layer below
and provides services to the layer above.

Now it is possible to simply add or remove components on a layer without having
to inspect big parts of code, dealing with redundancies, subtle dependencies,
etc. This also addresses a suggestion from a review we have received in the past.

*** SECOND CHANGE ***
The software does not "depend" on Z3 anymore. Now Z3 is just a component in the
lowest layer of the stack, represented by just one single file. Now that file is
the only one which imports the Z3 library, all the other files do not use Z3
code at all, e.g. the unbounded binary search and branch and bound are
independent of Z3 now.

If needed, another incremental Z3 solver with a Python API (like the ones from
Trento) can be used instead of Z3, without needing to change anything else in
the software. It is just sufficient to implement some trivial functions which
are required in the lowest layer (the "feasibility checking" layer).

*** THIRD CHANGE ***

The "naive" algorithm has been added as a component in the "CR optimization"
layer (CR stands for "Continuous Relaxation"). It has been tested and it is
perfectly working. In the past, this algorithm has only been tested for the
NLP case, as it was too complicated to change all the code to combine it with
other approaches like branch and bound. Now it has been reimplemented from
scratch and it has just been put in its layer and it works without problems.

*** FOURTH CHANGE ***

The "hybrid" algorithm has been added as a component in the "CR optimization"
layer. It seems to work perfectly, and it can now been compared with "naive",
"unbounded binary search" and with their simple parallel combination, to see
whether this version might replace the others as it is an interaction between
naive and u.b.s in which they "help each other".
