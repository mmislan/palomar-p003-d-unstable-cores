# A counterexample to D-unstable-core necessity

Michael Mislan

Vassena and Stadler conjectured that a reaction network with parameter-rich kinetics cannot have a Hurwitz-unstable Jacobian unless it contains a D-unstable core, a minimal square child-selection submatrix that becomes unstable under positive column scaling. We show that this conjecture is false. We construct a consistent reaction network with four species and five reactions and an admissible reactivity matrix for which the Jacobian has an eigenvalue with strictly positive real part, yet the network has no D-unstable core. Consistency is witnessed by a strictly positive stoichiometric kernel flux, and reactivities are positive exactly on reactant incidences. The counterexample and the resulting negation of the universal necessity statement are proved in Lean 4 with Mathlib.

[Result and formal statement](entries/P003/README.md) Â·
[Metadata](entries/P003/formalization.yaml) Â·
[Manuscript](papers/P003/paper.pdf) Â·
[Claim-to-evidence correspondence](entries/P003/CLAIM-EVIDENCE.md)

The project uses the exact Lean and Mathlib versions in `lean-toolchain` and
`lake-manifest.json`. The selected declaration, modules and permitted axioms are
specified in [the Comparator configuration](entries/P003/comparator.json).

The entry documentation links the retained local verification evidence and
describes its scope. This snapshot contains the substantive proof sources.
