import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Mul

/-!
# Failure of D-unstable-core necessity for parameter-rich networks

The statement negates the necessity assertion already for four species and five
reactions. Consistency means a strictly positive stoichiometric kernel flux;
reactivity entries are independently tunable and positive exactly on reactant
incidences. Instability means an eigenvalue with strictly positive real part.
A D-unstable core is a principal-minimal child selection unstable under some
positive right diagonal scaling. Explicit catalyst incidence is retained.

This is P003's parameter-rich counterexample to the Vassena–Stadler question.
No claim about classical mass-action realizability or an attracting orbit is
made by this entry. All local definitions needed to read the assertion are
included below, with the same definitions as the proof development.
-/

namespace AutocatalyticCS

/-- Nonnegative integer reactant and product multiplicities. -/
structure ReactionNetwork (X R : Type*) where
  reactant : X → R → ℕ
  product : X → R → ℕ

namespace ReactionNetwork
/-- Net stoichiometric coefficient: products minus reactants. -/
def net {X R : Type*} (Q : ReactionNetwork X R) (x : X) (r : R) : ℤ :=
  (Q.product x r : ℤ) - (Q.reactant x r : ℤ)
end ReactionNetwork

variable {X R : Type*} [DecidableEq X] [DecidableEq R]

/-- Equally many selected species and reactions, bijectively matched along
literal reactant incidences. -/
structure ChildSelection (Q : ReactionNetwork X R) where
  species : Finset X
  reactions : Finset R
  assign : {x // x ∈ species} ≃ {r // r ∈ reactions}
  reactant_match : ∀ x, 0 < Q.reactant x.1 (assign x).1

namespace ChildSelection
variable {Q : ReactionNetwork X R}
/-- Square stoichiometric submatrix, columns indexed by their matched species. -/
def matrix (κ : ChildSelection Q) : Matrix κ.species κ.species ℤ :=
  fun x y => Q.net x.1 (κ.assign y).1

/-- Principal restriction retains both supports and the assignment on species. -/
def Restricts (κ₁ κ₂ : ChildSelection Q) : Prop :=
  κ₁.species ⊆ κ₂.species ∧
  κ₁.reactions ⊆ κ₂.reactions ∧
  ∀ (x₁ : {x // x ∈ κ₁.species}) (x₂ : {x // x ∈ κ₂.species}),
    x₁.1 = x₂.1 → (κ₁.assign x₁).1 = (κ₂.assign x₂).1
end ChildSelection
end AutocatalyticCS

namespace DUnstableCores
open scoped BigOperators

/-- Literal reaction multiplicities and explicit catalysts present on both sides. -/
structure SourceNetwork (Species Reaction : Type*) where
  reactant : Matrix Species Reaction ℕ
  product : Matrix Species Reaction ℕ
  catalyst : Matrix Species Reaction ℕ
  catalyst_le_reactant : ∀ s r, catalyst s r ≤ reactant s r
  catalyst_le_product : ∀ s r, catalyst s r ≤ product s r

namespace SourceNetwork
variable {Species Reaction : Type*}
/-- Net integer stoichiometric matrix. -/
def stoich (Q : SourceNetwork Species Reaction) : Matrix Species Reaction ℤ :=
  fun s r => (Q.product s r : ℤ) - (Q.reactant s r : ℤ)
/-- Forget catalyst labels without deleting reactant multiplicities. -/
def toReactionNetwork (Q : SourceNetwork Species Reaction) :
    AutocatalyticCS.ReactionNetwork Species Reaction where
  reactant := Q.reactant
  product := Q.product
/-- A species occurs as a reactant with positive multiplicity. -/
def Reactant (Q : SourceNetwork Species Reaction) (s : Species) (r : Reaction) : Prop :=
  0 < Q.reactant s r
end SourceNetwork

variable {Species Reaction : Type*}
/-- Child selection on the literal source, including explicit-catalyst incidences. -/
abbrev ChildSelection (Q : SourceNetwork Species Reaction) :=
  AutocatalyticCS.ChildSelection Q.toReactionNetwork

namespace ChildSelection
variable {Q : SourceNetwork Species Reaction}
/-- The same-assignment restriction order on children. -/
abbrev Restricts [DecidableEq Species] [DecidableEq Reaction]
    (small large : ChildSelection Q) : Prop :=
  AutocatalyticCS.ChildSelection.Restricts small large
end ChildSelection

/-- An admissible parameter-rich derivative matrix, positive precisely on
reactant incidences and zero elsewhere. -/
structure Reactivity (Q : SourceNetwork Species Reaction) where
  value : Matrix Reaction Species ℝ
  nonneg : ∀ r s, 0 ≤ value r s
  positive_of_reactant : ∀ r s, Q.Reactant s r → 0 < value r s
  zero_of_not_reactant : ∀ r s, ¬ Q.Reactant s r → value r s = 0

namespace SourceNetwork
variable [Fintype Reaction]
/-- A strictly positive reaction flux lies in the stoichiometric kernel. -/
def Consistent (Q : SourceNetwork Species Reaction) : Prop :=
  ∃ flux : Reaction → ℝ,
    (∀ r, 0 < flux r) ∧
      ∀ s, ∑ r : Reaction, (Q.stoich s r : ℝ) * flux r = 0
/-- The full parameter-rich Jacobian S R. -/
def jacobian (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    Matrix Species Species ℝ :=
  fun i j => ∑ r : Reaction, (Q.stoich i r : ℝ) * R.value r j
end SourceNetwork

universe u_1
variable {ι : Type u_1}
/-- Positive diagonal scaling acts on columns (right multiplication). -/
def rightScale (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * d j
/-- Entrywise inclusion of real matrices in complex matrices. -/
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)
/-- A nonzero complex eigenvector and its eigenvalue. -/
def HasEigenpair [Fintype ι] (A : Matrix ι ι ℝ) (lam : ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ ∀ i, Matrix.mulVec (complexify A) v i = lam * v i
/-- At least one eigenvalue lies strictly in the open right half-plane. -/
def HurwitzUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ lam : ℂ, ∃ v : ι → ℂ, 0 < lam.re ∧ HasEigenpair A lam v
/-- Some strictly positive right diagonal scaling is Hurwitz-unstable. -/
def DUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ HurwitzUnstable (rightScale A d)

end DUnstableCores

namespace DUnstableCores
variable {Species Reaction : Type*}
section Minimality
variable [DecidableEq Species] [DecidableEq Reaction]
variable {Q : SourceNetwork Species Reaction}
namespace ChildSelection
/-- Child stoichiometric matrix over the reals. -/
def realMatrix (κ : ChildSelection Q) : Matrix κ.species κ.species ℝ :=
  fun i j => (κ.matrix i j : ℝ)
end ChildSelection
/-- A D-unstable child with no D-unstable proper principal restriction. -/
def IsDUnstableCore (κ : ChildSelection Q) : Prop :=
  DUnstable κ.realMatrix ∧
    ∀ small : ChildSelection Q,
      small.Restricts κ → small.species ⊂ κ.species →
        ¬ DUnstable small.realMatrix
end Minimality

/-- The consistency-scoped necessity assertion is false for four species and
five reactions, with all incidences, scalings, and spectral conditions as above. -/
theorem parameterRich_consistent_core_necessity_fin4_fin5_false :
    ¬ (∀ (Q : SourceNetwork (Fin 4) (Fin 5)), Q.Consistent →
      ∀ R : Reactivity Q, HurwitzUnstable (Q.jacobian R) →
        ∃ core : ChildSelection Q, IsDUnstableCore core) := by
  sorry
end DUnstableCores
