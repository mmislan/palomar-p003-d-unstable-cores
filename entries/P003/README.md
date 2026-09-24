# P003: An exact counterexample to the D-unstable-core conjecture for parameter-rich reaction networks

Author: Michael Mislan.

Literature problem numbers: 6.

Vassena and Stadler conjectured that a reaction network with parameter-rich kinetics cannot have a Hurwitz-unstable Jacobian unless it contains a D-unstable core, a minimal square child-selection submatrix that becomes unstable under positive column scaling. We show that this conjecture is false. We construct a consistent reaction network with four species and five reactions and an admissible reactivity matrix for which the Jacobian has an eigenvalue with strictly positive real part, yet the network has no D-unstable core. Consistency is witnessed by a strictly positive stoichiometric kernel flux, and reactivities are positive exactly on reactant incidences. The counterexample and the resulting negation of the universal necessity statement are proved in Lean 4 with Mathlib.

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
