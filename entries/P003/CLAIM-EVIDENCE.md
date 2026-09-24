# P003: claim-to-evidence correspondence

Source-reading review dated 2026-09-23. No Lean was executed for this review.

| Mathematical content | Formal source | Evidence |
|---|---|---|
| Failure of universal core necessity for four species and five reactions | `parameterRich_consistent_core_necessity_fin4_fin5_false` | Selected by Comparator; retained complete local mechanical pass. |
| Positive stoichiometric kernel flux | `SourceNetwork.Consistent`; `parameterRichCounterexampleSource_consistent` | Explicit Challenge hypothesis supplied by the witness. |
| Reactivity positive on reactant incidences and zero elsewhere | `Reactivity`; `parameterRichCounterexampleReactivity` | Required by the formal structure. |
| Strictly positive real part of a Jacobian eigenvalue | `HurwitzUnstable`; `parameterRichCounterexample_hurwitzUnstable` | Constructed through the explicit eigenpair in the proof. |
| Absence of a D-unstable core | `parameterRichCounterexample_no_dUnstableCore` | Follows from the all-children D-noninstability theorem and is used by the selected declaration. |
| Literal child selections and principal minimality | `ChildSelection`, `Restricts`, `IsDUnstableCore` | Definitions occur in the Challenge and were compared with the proof environment. |

Names are in `DUnstableCores` except the underlying `AutocatalyticCS.ChildSelection`
definitions. See [the proof source](../../proofs/DUnstableCores/ParameterRichCounterexample.lean).
The manuscript's main theorem supplies the concrete witness and interpretation.

## Literature correspondence

[Vassena–Stadler, arXiv:2308.11486v3, Section 5](https://arxiv.org/html/2308.11486v3#S5)
states the necessity conjecture and defines cores by principal minimality.
The Challenge makes the positive-flux condition, admissible reactivities and
spectral meaning explicit. A finite consistent counterexample negates the
universal assertion. This is an agent-assisted reading of the definitions and
primary source, not an independent human referee report.

## Evidence boundary

The compared declaration is a Jacobian/core assertion. The manuscript's explicit
generalized-mass-action realization interprets those algebraic data as a kinetic
system. The public description states the Jacobian result directly. This review
does not certify every manuscript argument.

The [retained receipt](../../preparation/verification/P003-ninth-run/result.json)
establishes the recorded mechanical comparison. The editorial correspondence
above is a source-reading assessment. Metadata edits are not a new proof run.
Earlier pending-verification comments in preserved Lean sources describe an
earlier stage and are superseded by the receipt.
