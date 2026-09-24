# P003: An exact counterexample to the D-unstable-core conjecture for parameter-rich reaction networks

Author: Michael Mislan.

Literature problem numbers: 6.

Vassena and Stadler introduced unstable cores, minimal square child-selection submatrices of the stoichiometric matrix, and proved that a D-unstable core is sufficient for a reaction network with parameter-rich kinetics to admit an unstable positive equilibrium. They conjectured the converse: a network without D-unstable cores cannot have a Hurwitz-unstable Jacobian. We show that this conjecture is false. We exhibit a reaction network with four species and five reactions, no catalysts, and a strictly positive equilibrium flux, together with an admissible reactivity matrix for which the Jacobian $G = SR$ has the eigenvalue $\frac{1}{500} + \frac{51}{500}i$, while every one of its 24 child-selection matrices is D-nonunstable, so that no D-unstable core exists. All data are rational, the eigenvector is a Gaussian-integer vector, and the child certificates are exact: three positive-semidefinite weighted symmetrizations, one exact cubic factorization $X(X + 4d_0)(X + 4d_1 + 2d_2)$, and two two-dimensional faces. The source-network construction and the negation of the universal necessity statement are verified in Lean 4 with Mathlib. The companion manuscript gives an explicit generalized-mass-action realization of the unstable equilibrium and explains the collective obstruction.

The result addresses Conjecture 17 of Nicola Vassena and Peter F. Stadler,
[Unstable Cores are the source of instability in chemical reaction networks](https://arxiv.org/html/2308.11486v3#S5),
Proceedings of the Royal Society A 480 (2024), 20230694,
[doi:10.1098/rspa.2023.0694](https://doi.org/10.1098/rspa.2023.0694).
Its subject is the relation between stoichiometric submatrices and spectral instability.

[Companion manuscript](../../papers/P003/paper.pdf) Â· [Metadata](formalization.yaml) Â· [Readiness](readiness.json)

The [claim-to-evidence table](CLAIM-EVIDENCE.md) describes the selected assertion,
its definitions and its correspondence with the literature question.

## Formal statement

[Challenge](../../Registry/P003/Challenge.lean) Â· [Solution](../../Registry/P003/Solution.lean) Â· [Comparator](comparator.json)

The Challenge and Solution compile on the pinned target toolchain. Exact Comparator comparison, allowed-axiom validation, con-ron, nanoda, and Lean kernel checks passed. The selected declaration is:

- `DUnstableCores.parameterRich_consistent_core_necessity_fin4_fin5_false`

## Verification evidence

The [release-candidate receipt](../../preparation/verification/P003-release-candidate-run/result.json)
and [verifier log](../../preparation/verification/P003-release-candidate-run/comparator.log)
record a successful check completed on 2026-09-24 at 15:00 UTC, including
Comparator, con-ron, NanoDa and Lean kernel checks. The selected proof sources,
Challenge/Solution modules, Comparator configuration, Lake configuration and
pinned dependencies match that run byte for byte. Documentation and a manually
triggered submission workflow were prepared afterwards; no proof rerun was used
for those changes. Registry verification and editorial review are separate.
