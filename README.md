# A counterexample to D-unstable-core necessity

Michael Mislan

Vassena and Stadler introduced unstable cores, minimal square child-selection submatrices of the stoichiometric matrix, and proved that a D-unstable core is sufficient for a reaction network with parameter-rich kinetics to admit an unstable positive equilibrium. They conjectured the converse: a network without D-unstable cores cannot have a Hurwitz-unstable Jacobian. We show that this conjecture is false. We exhibit a reaction network with four species and five reactions, no catalysts, and a strictly positive equilibrium flux, together with an admissible reactivity matrix for which the Jacobian $G = SR$ has the eigenvalue $\frac{1}{500} + \frac{51}{500}i$, while every one of its 24 child-selection matrices is D-nonunstable, so that no D-unstable core exists. All data are rational, the eigenvector is a Gaussian-integer vector, and the child certificates are exact: three positive-semidefinite weighted symmetrizations, one exact cubic factorization $X(X + 4d_0)(X + 4d_1 + 2d_2)$, and two two-dimensional faces. The source-network construction and the negation of the universal necessity statement are verified in Lean 4 with Mathlib. The companion manuscript gives an explicit generalized-mass-action realization of the unstable equilibrium and explains the collective obstruction.

[Result and formal statement](entries/P003/README.md) Â·
[Metadata](entries/P003/formalization.yaml) Â·
[Manuscript](papers/P003/paper.pdf) Â·
[Claim-to-evidence correspondence](entries/P003/CLAIM-EVIDENCE.md)

The project uses the exact Lean and Mathlib versions in `lean-toolchain` and
`lake-manifest.json`. The selected declaration, modules and permitted axioms are
specified in [the Comparator configuration](entries/P003/comparator.json).

The entry documentation links the retained local verification evidence and
describes its scope. This snapshot contains the substantive proof sources.
