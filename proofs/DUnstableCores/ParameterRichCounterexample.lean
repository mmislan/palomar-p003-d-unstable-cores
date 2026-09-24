import proofs.AutocatalyticCS.MatchingIndex
import proofs.DUnstableCores.Minimality
import proofs.DUnstableCores.RouthHurwitzDim3
import proofs.DUnstableCores.CubicCoefficientsDim3
import proofs.DUnstableCores.DiagonalDissipative
import proofs.DUnstableCores.ReindexDNon
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A parameter-rich counterexample to D-unstable-core necessity

The integer source below has four maximal child matchings.  Every one admits
an exact diagonal energy certificate, whereas one admissible independently
tunable reactivity gives the full source Jacobian a strict open-right-half-
plane conjugate pair.
-/

namespace DUnstableCores

open Polynomial

set_option linter.unusedSimpArgs false

/-- The symmetric matrix whose nonnegativity is the diagonal-energy
certificate for `A` with row weights `p`. -/
def weightedSymmetrization {ι : Type*}
    (A : Matrix ι ι ℝ) (p : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => -(p i * A i j + p j * A j i)

theorem weightedSymmetrization_isHermitian {ι : Type*}
    (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    (weightedSymmetrization A p).IsHermitian := by
  ext i j
  simp [weightedSymmetrization]
  ring

/-- A positive-semidefinite weighted symmetrization is exactly the convenient
principal-submatrix-stable form of a diagonal dissipativity certificate. -/
theorem weightedDissipative_of_posSemidef {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (hp : ∀ i, 0 < p i)
    (hpsd : (weightedSymmetrization A p).PosSemidef) :
    WeightedDissipative A p := by
  constructor
  · exact hp
  · intro x y
    have hx := hpsd.dotProduct_mulVec_nonneg x
    have hy := hpsd.dotProduct_mulVec_nonneg y
    simp only [weightedSymmetrization, dotProduct, Matrix.mulVec,
      star_trivial] at hx hy
    simp_rw [Finset.mul_sum] at hx hy
    rw [Finset.sum_comm] at hx hy
    ring_nf at hx hy
    simp_rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hx hy
    have hswapx :
        (∑ i, ∑ j, x j * p j * A j i * x i) =
          ∑ i, ∑ j, x j * p i * A i j * x i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hswapy :
        (∑ i, ∑ j, y j * p j * A j i * y i) =
          ∑ i, ∑ j, y j * p i * A i j * y i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hswapx] at hx
    rw [hswapy] at hy
    have htermx :
        (∑ i, ∑ j, x j * p i * A i j * x i) =
          ∑ i, ∑ j, p i * x i * x j * A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htermy :
        (∑ i, ∑ j, y j * p i * A i j * y i) =
          ∑ i, ∑ j, p i * y i * y j * A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [htermx] at hx
    rw [htermy] at hy
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [Finset.mul_sum]
    ring_nf at hx hy ⊢
    rw [Finset.sum_add_distrib]
    ring_nf
    have henergyx :
        (∑ i, p i * ∑ j, x i * A i j * x j) =
          ∑ i, ∑ j, p i * x i * x j * A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have henergyy :
        (∑ i, p i * ∑ j, y i * A i j * y j) =
          ∑ i, ∑ j, p i * y i * y j * A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [henergyx, henergyy]
    nlinarith [hx, hy]

/-- Weighted dissipativity passes to every principal submatrix. -/
theorem weightedDissipative_submatrix {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (hpsd : (weightedSymmetrization A p).PosSemidef)
    (hp : ∀ i, 0 < p i) (f : κ → ι) :
    WeightedDissipative (A.submatrix f f) (fun i => p (f i)) := by
  apply weightedDissipative_of_posSemidef (fun i => hp (f i))
  have hsub := hpsd.submatrix f
  convert hsub using 1
  ext i j
  rfl

theorem weightedSym_posSemidef_of_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (e : κ ≃ ι) (w : κ → ℝ)
    (hmat : Matrix.reindex e.symm e.symm A = B)
    (hB : (weightedSymmetrization B w).PosSemidef) :
    (weightedSymmetrization A (fun i => w (e.symm i))).PosSemidef := by
  rw [← Matrix.posSemidef_submatrix_equiv e]
  have heq :
      (weightedSymmetrization A (fun i => w (e.symm i))).submatrix e e =
        weightedSymmetrization (Matrix.reindex e.symm e.symm A) w := by
    ext i j
    simp [weightedSymmetrization, Matrix.reindex_apply]
  rw [heq]
  rw [hmat]
  exact hB

/-- The four-reaction matrix witness has trivial reaction-flux kernel and is
therefore only a matrix-level counterexample, not yet a literature-scoped
reaction-network counterexample. -/
def parameterRichInconsistentCounterexampleSource : SourceNetwork (Fin 4) (Fin 4) where
  reactant := !![1, 0, 0, 0;
                 0, 4, 0, 0;
                 0, 2, 4, 0;
                 2, 0, 0, 2]
  product := !![0, 0, 0, 1;
                0, 0, 0, 6;
                4, 0, 0, 1;
                0, 0, 2, 0]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

/-- The original four-reaction source has no strictly positive kernel flux. -/
theorem parameterRichInconsistentCounterexampleSource_not_consistent :
    ¬ parameterRichInconsistentCounterexampleSource.Consistent := by
  rintro ⟨flux, hpos, hker⟩
  have h0 := hker (0 : Fin 4)
  have h1 := hker (1 : Fin 4)
  have h2 := hker (2 : Fin 4)
  have h3 := hker (3 : Fin 4)
  simp [SourceNetwork.Consistent, SourceNetwork.stoich,
    parameterRichInconsistentCounterexampleSource, Fin.sum_univ_four] at h0 h1 h2 h3
  have hp0 := hpos (0 : Fin 4)
  linarith

/-- The literature-scoped source appends the reactant-free inflow
`∅ → 2 X₂ + 2 X₃`.  Its stoichiometry is
`[[-1,0,0,1,0],[0,-4,0,6,0],[4,-2,-4,1,2],[-2,0,2,-2,2]]`. -/
def parameterRichCounterexampleSource : SourceNetwork (Fin 4) (Fin 5) where
  reactant := !![1, 0, 0, 0, 0;
                 0, 4, 0, 0, 0;
                 0, 2, 4, 0, 0;
                 2, 0, 0, 2, 0]
  product := !![0, 0, 0, 1, 0;
                0, 0, 0, 6, 0;
                4, 0, 0, 1, 2;
                0, 0, 2, 0, 2]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

/-- Exact strictly positive equilibrium-flux witness `(2,3,2,2,2)`. -/
theorem parameterRichCounterexampleSource_consistent :
    parameterRichCounterexampleSource.Consistent := by
  refine ⟨![2, 3, 2, 2, 2], ?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num
  · intro s
    fin_cases s <;>
      norm_num [SourceNetwork.Consistent, SourceNetwork.stoich,
        parameterRichCounterexampleSource, Fin.sum_univ_succ]

def parameterRichCounterexampleMax2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2, 4; 0, -2]

def parameterRichCounterexampleMax3a : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 1; 4, -2, 1; -2, 0, -2]

def parameterRichCounterexampleMax3b : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-4, 0, 0; -2, -4, 4; 0, 2, -2]

def parameterRichCounterexampleMax4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 1; 0, -4, 0, 6; 4, -2, -4, 1; -2, 0, 2, -2]

def parameterRichCounterexampleWeight2 : Fin 2 → ℝ := ![1, 2]
def parameterRichCounterexampleWeight3a : Fin 3 → ℝ := ![10, 2, 7]
def parameterRichCounterexampleWeight4 : Fin 4 → ℝ := ![100, 35, 40, 140]

def parameterRichCounterexampleFace13 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-4, 0; 0, -2]

def parameterRichCounterexampleFace23 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-4, 4; 2, -2]

def parameterRichCounterexampleFaceWeight : Fin 2 → ℝ := ![1, 2]

theorem parameterRichCounterexampleMax2_psd :
    (weightedSymmetrization parameterRichCounterexampleMax2
      parameterRichCounterexampleWeight2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightedSymmetrization_isHermitian _ _)
  intro x
  have h0 : 0 ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (x 1) ^ 2 := sq_nonneg _
  simp [weightedSymmetrization, parameterRichCounterexampleMax2,
    parameterRichCounterexampleWeight2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  nlinarith

theorem parameterRichCounterexampleMax3a_psd :
    (weightedSymmetrization parameterRichCounterexampleMax3a
      parameterRichCounterexampleWeight3a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightedSymmetrization_isHermitian _ _)
  intro x
  have h0 : 0 ≤ (5 * x 0 - 2 * x 1 + x 2) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (12 * x 1 - x 2) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (x 2) ^ 2 := sq_nonneg _
  simp [weightedSymmetrization, parameterRichCounterexampleMax3a,
    parameterRichCounterexampleWeight3a, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  nlinarith

theorem parameterRichCounterexampleMax4_psd :
    (weightedSymmetrization parameterRichCounterexampleMax4
      parameterRichCounterexampleWeight4).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightedSymmetrization_isHermitian _ _)
  intro x
  have h0 : 0 ≤ (10 * x 0 - 8 * x 2 + 9 * x 3) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (28 * x 1 + 8 * x 2 - 21 * x 3) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (296 * x 2 - 203 * x 3) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (x 3) ^ 2 := sq_nonneg _
  simp [weightedSymmetrization, parameterRichCounterexampleMax4,
    parameterRichCounterexampleWeight4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  nlinarith

theorem parameterRichCounterexampleFace13_psd :
    (weightedSymmetrization parameterRichCounterexampleFace13
      parameterRichCounterexampleFaceWeight).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightedSymmetrization_isHermitian _ _)
  intro x
  have h0 : 0 ≤ (x 0) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (x 1) ^ 2 := sq_nonneg _
  simp [weightedSymmetrization, parameterRichCounterexampleFace13,
    parameterRichCounterexampleFaceWeight, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  nlinarith

theorem parameterRichCounterexampleFace23_psd :
    (weightedSymmetrization parameterRichCounterexampleFace23
      parameterRichCounterexampleFaceWeight).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightedSymmetrization_isHermitian _ _)
  intro x
  have h0 : 0 ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
  simp [weightedSymmetrization, parameterRichCounterexampleFace23,
    parameterRichCounterexampleFaceWeight, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  nlinarith

abbrev parameterRichCounterexampleMatching2 :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 2
  left := ![2, 3]
  right := ![1, 0]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

abbrev parameterRichCounterexampleMatching3a :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 3
  left := ![0, 2, 3]
  right := ![0, 1, 3]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

abbrev parameterRichCounterexampleMatching3b :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 3
  left := ![1, 2, 3]
  right := ![1, 2, 0]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

abbrev parameterRichCounterexampleMatching4 :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 4
  left := ![0, 1, 2, 3]
  right := ![0, 1, 2, 3]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

abbrev parameterRichCounterexampleMatching13 :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 2
  left := ![1, 3]
  right := ![1, 0]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

abbrev parameterRichCounterexampleMatching23 :
    AutocatalyticCS.IndexedMatching parameterRichCounterexampleSource.toReactionNetwork where
  card := 2
  left := ![2, 3]
  right := ![2, 0]
  left_injective := by decide
  right_injective := by decide
  reactant_edge := by decide

@[simp] theorem indexedMatching_indexSpeciesEquiv_val
    {Reaction : Type*} [DecidableEq Reaction]
    {Q : AutocatalyticCS.ReactionNetwork (Fin 4) Reaction}
    (E : AutocatalyticCS.IndexedMatching Q) (i : Fin E.card) :
    (E.indexSpeciesEquiv i).1 = E.left i := rfl

theorem parameterRichCounterexampleMatching2_matrix :
    Matrix.reindex parameterRichCounterexampleMatching2.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching2.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching2.toChildSelection) =
      parameterRichCounterexampleMax2 := by
  ext i j
  change ((parameterRichCounterexampleMatching2.toChildSelection.matrix
    (parameterRichCounterexampleMatching2.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching2.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching2.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching2.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching2.assign
    (parameterRichCounterexampleMatching2.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching2.right j at hj
  rw [hj]
  rw [indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching2] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleMax2]

theorem parameterRichCounterexampleMatching3a_matrix :
    Matrix.reindex parameterRichCounterexampleMatching3a.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching3a.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching3a.toChildSelection) =
      parameterRichCounterexampleMax3a := by
  ext i j
  change ((parameterRichCounterexampleMatching3a.toChildSelection.matrix
    (parameterRichCounterexampleMatching3a.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching3a.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching3a.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching3a.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching3a.assign
    (parameterRichCounterexampleMatching3a.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching3a.right j at hj
  rw [hj]
  rw [indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching3a] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleMax3a]

theorem parameterRichCounterexampleMatching3b_matrix :
    Matrix.reindex parameterRichCounterexampleMatching3b.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching3b.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching3b.toChildSelection) =
      parameterRichCounterexampleMax3b := by
  ext i j
  change ((parameterRichCounterexampleMatching3b.toChildSelection.matrix
    (parameterRichCounterexampleMatching3b.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching3b.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching3b.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching3b.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching3b.assign
    (parameterRichCounterexampleMatching3b.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching3b.right j at hj
  rw [hj]
  rw [indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching3b] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleMax3b]

theorem parameterRichCounterexampleMax3b_dNonUnstable :
    DNonUnstable parameterRichCounterexampleMax3b := by
  intro d hd
  have hd0 : 0 < d 0 := hd 0
  have hd1 : 0 < d 1 := hd 1
  have hd2 : 0 < d 2 := hd 2
  let a₁ : ℝ := 4 * d 0 + 4 * d 1 + 2 * d 2
  let a₂ : ℝ := 16 * d 0 * d 1 + 8 * d 0 * d 2
  have hc₁ : cubicCoeff1 (rightScale parameterRichCounterexampleMax3b d) = a₁ := by
    simp [cubicCoeff1, rightScale, parameterRichCounterexampleMax3b, a₁]
    ring
  have hc₂ : cubicCoeff2 (rightScale parameterRichCounterexampleMax3b d) = a₂ := by
    simp [cubicCoeff2, rightScale, parameterRichCounterexampleMax3b, a₂]
    ring
  have hc₃ : cubicCoeff3 (rightScale parameterRichCounterexampleMax3b d) = 0 := by
    simp [cubicCoeff3, rightScale, parameterRichCounterexampleMax3b,
      Matrix.det_fin_three]
    ring
  apply hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
    (rightScale parameterRichCounterexampleMax3b d) a₁ a₂ 0
  · rw [← hc₁, ← hc₂, ← hc₃]
    exact isCubicCharpoly_explicit _
  · dsimp [a₁]
    positivity
  · dsimp [a₂]
    positivity
  · norm_num
  · have ha₁ : 0 ≤ a₁ := by
      dsimp [a₁]
      positivity
    have ha₂ : 0 ≤ a₂ := by
      dsimp [a₂]
      positivity
    nlinarith

theorem parameterRichCounterexampleMatching4_matrix :
    Matrix.reindex parameterRichCounterexampleMatching4.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching4.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching4.toChildSelection) =
      parameterRichCounterexampleMax4 := by
  ext i j
  change ((parameterRichCounterexampleMatching4.toChildSelection.matrix
    (parameterRichCounterexampleMatching4.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching4.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching4.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching4.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching4.assign
    (parameterRichCounterexampleMatching4.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching4.right j at hj
  rw [hj]
  rw [indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching4] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleMax4]

theorem parameterRichCounterexampleMatching13_matrix :
    Matrix.reindex parameterRichCounterexampleMatching13.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching13.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching13.toChildSelection) =
      parameterRichCounterexampleFace13 := by
  ext i j
  change ((parameterRichCounterexampleMatching13.toChildSelection.matrix
    (parameterRichCounterexampleMatching13.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching13.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching13.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching13.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching13.assign
    (parameterRichCounterexampleMatching13.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching13.right j at hj
  rw [hj, indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching13] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleFace13]

theorem parameterRichCounterexampleMatching23_matrix :
    Matrix.reindex parameterRichCounterexampleMatching23.indexSpeciesEquiv.symm
        parameterRichCounterexampleMatching23.indexSpeciesEquiv.symm
        (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
          parameterRichCounterexampleMatching23.toChildSelection) =
      parameterRichCounterexampleFace23 := by
  ext i j
  change ((parameterRichCounterexampleMatching23.toChildSelection.matrix
    (parameterRichCounterexampleMatching23.indexSpeciesEquiv i)
    (parameterRichCounterexampleMatching23.indexSpeciesEquiv j) : ℤ) : ℝ) = _
  erw [parameterRichCounterexampleMatching23.toChildSelection_matrix]
  have hj := parameterRichCounterexampleMatching23.toChildSelection_assign_indexSpeciesEquiv j
  change (parameterRichCounterexampleMatching23.assign
    (parameterRichCounterexampleMatching23.indexSpeciesEquiv j)).1 =
      parameterRichCounterexampleMatching23.right j at hj
  rw [hj, indexedMatching_indexSpeciesEquiv_val]
  fin_cases i <;> fin_cases j <;>
    simp only [parameterRichCounterexampleMatching23] <;>
    simp [parameterRichCounterexampleSource, SourceNetwork.stoich,
      parameterRichCounterexampleFace23]

theorem parameterRichCounterexampleMatching2_psd :
    (weightedSymmetrization
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching2.toChildSelection)
      (fun i => parameterRichCounterexampleWeight2
        (parameterRichCounterexampleMatching2.indexSpeciesEquiv.symm i))).PosSemidef :=
  weightedSym_posSemidef_of_reindex _ _ _ _
    parameterRichCounterexampleMatching2_matrix parameterRichCounterexampleMax2_psd

theorem parameterRichCounterexampleMatching3a_psd :
    (weightedSymmetrization
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching3a.toChildSelection)
      (fun i => parameterRichCounterexampleWeight3a
        (parameterRichCounterexampleMatching3a.indexSpeciesEquiv.symm i))).PosSemidef :=
  weightedSym_posSemidef_of_reindex _ _ _ _
    parameterRichCounterexampleMatching3a_matrix parameterRichCounterexampleMax3a_psd

theorem parameterRichCounterexampleMatching4_psd :
    (weightedSymmetrization
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching4.toChildSelection)
      (fun i => parameterRichCounterexampleWeight4
        (parameterRichCounterexampleMatching4.indexSpeciesEquiv.symm i))).PosSemidef :=
  weightedSym_posSemidef_of_reindex _ _ _ _
    parameterRichCounterexampleMatching4_matrix parameterRichCounterexampleMax4_psd

theorem parameterRichCounterexampleMatching13_psd :
    (weightedSymmetrization
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching13.toChildSelection)
      (fun i => parameterRichCounterexampleFaceWeight
        (parameterRichCounterexampleMatching13.indexSpeciesEquiv.symm i))).PosSemidef :=
  weightedSym_posSemidef_of_reindex _ _ _ _
    parameterRichCounterexampleMatching13_matrix parameterRichCounterexampleFace13_psd

theorem parameterRichCounterexampleMatching23_psd :
    (weightedSymmetrization
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching23.toChildSelection)
      (fun i => parameterRichCounterexampleFaceWeight
        (parameterRichCounterexampleMatching23.indexSpeciesEquiv.symm i))).PosSemidef :=
  weightedSym_posSemidef_of_reindex _ _ _ _
    parameterRichCounterexampleMatching23_matrix parameterRichCounterexampleFace23_psd

theorem parameterRichCounterexampleMatching2_weight_pos
    (i : parameterRichCounterexampleMatching2.toChildSelection.species) :
    0 < parameterRichCounterexampleWeight2
      (parameterRichCounterexampleMatching2.indexSpeciesEquiv.symm i) := by
  have h : ∀ k : Fin 2, 0 < parameterRichCounterexampleWeight2 k := by
    intro k
    fin_cases k <;> norm_num [parameterRichCounterexampleWeight2]
  exact h _

theorem parameterRichCounterexampleMatching3a_weight_pos
    (i : parameterRichCounterexampleMatching3a.toChildSelection.species) :
    0 < parameterRichCounterexampleWeight3a
      (parameterRichCounterexampleMatching3a.indexSpeciesEquiv.symm i) := by
  have h : ∀ k : Fin 3, 0 < parameterRichCounterexampleWeight3a k := by
    intro k
    fin_cases k <;> norm_num [parameterRichCounterexampleWeight3a]
  exact h _

theorem parameterRichCounterexampleMatching4_weight_pos
    (i : parameterRichCounterexampleMatching4.toChildSelection.species) :
    0 < parameterRichCounterexampleWeight4
      (parameterRichCounterexampleMatching4.indexSpeciesEquiv.symm i) := by
  have h : ∀ k : Fin 4, 0 < parameterRichCounterexampleWeight4 k := by
    intro k
    fin_cases k <;> norm_num [parameterRichCounterexampleWeight4]
  exact h _

theorem parameterRichCounterexampleMatching13_weight_pos
    (i : parameterRichCounterexampleMatching13.toChildSelection.species) :
    0 < parameterRichCounterexampleFaceWeight
      (parameterRichCounterexampleMatching13.indexSpeciesEquiv.symm i) := by
  have h : ∀ k : Fin 2, 0 < parameterRichCounterexampleFaceWeight k := by
    intro k
    fin_cases k <;> norm_num [parameterRichCounterexampleFaceWeight]
  exact h _

theorem parameterRichCounterexampleMatching23_weight_pos
    (i : parameterRichCounterexampleMatching23.toChildSelection.species) :
    0 < parameterRichCounterexampleFaceWeight
      (parameterRichCounterexampleMatching23.indexSpeciesEquiv.symm i) := by
  have h : ∀ k : Fin 2, 0 < parameterRichCounterexampleFaceWeight k := by
    intro k
    fin_cases k <;> norm_num [parameterRichCounterexampleFaceWeight]
  exact h _

theorem parameterRichCounterexampleMatching3b_dNonUnstable :
    DNonUnstable
      (ChildSelection.realMatrix (Q := parameterRichCounterexampleSource)
        parameterRichCounterexampleMatching3b.toChildSelection) := by
  apply (dNonUnstable_reindex_iff
    parameterRichCounterexampleMatching3b.indexSpeciesEquiv.symm _).mp
  rw [parameterRichCounterexampleMatching3b_matrix]
  exact parameterRichCounterexampleMax3b_dNonUnstable

def childRestrictionEmbedding
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {small large : ChildSelection Q}
    (h : small.Restricts large) : small.species → large.species :=
  fun x => ⟨x.1, h.1 x.2⟩

theorem child_realMatrix_eq_restriction
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {small large : ChildSelection Q}
    (h : small.Restricts large) :
    small.realMatrix = large.realMatrix.submatrix
      (childRestrictionEmbedding h) (childRestrictionEmbedding h) := by
  ext i j
  change ((Q.stoich i.1 (small.assign j).1 : ℤ) : ℝ) =
    ((Q.stoich i.1 (large.assign (childRestrictionEmbedding h j)).1 : ℤ) : ℝ)
  rw [h.2.2 j (childRestrictionEmbedding h j) rfl]

theorem dNonUnstable_of_restricts_psd
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {small large : ChildSelection Q}
    (h : small.Restricts large) (p : large.species → ℝ)
    (hp : ∀ i, 0 < p i)
    (hpsd : (weightedSymmetrization large.realMatrix p).PosSemidef) :
    DNonUnstable small.realMatrix := by
  rw [child_realMatrix_eq_restriction h]
  exact (weightedDissipative_submatrix hpsd hp
    (childRestrictionEmbedding h)).dNonUnstable

theorem childSelection_restricts_of_species_assign
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {small large : ChildSelection Q}
    (hs : small.species ⊆ large.species)
    (ha : ∀ (x : small.species) (y : large.species), x.1 = y.1 →
      (small.assign x).1 = (large.assign y).1) :
    small.Restricts large := by
  refine ⟨hs, ?_, ha⟩
  intro r hr
  obtain ⟨x, hx⟩ := small.assign.surjective ⟨r, hr⟩
  let y : large.species := ⟨x.1, hs x.2⟩
  have hxy := ha x y rfl
  have hval : (small.assign x).1 = r := congrArg Subtype.val hx
  rw [hval] at hxy
  rw [hxy]
  exact (large.assign y).2

theorem parameterRichCounterexample_assign_zero
    (κ : ChildSelection parameterRichCounterexampleSource) (x : κ.species)
    (hx : x.1 = 0) : (κ.assign x).1 = 0 := by
  have h := κ.reactant_match x
  simp [parameterRichCounterexampleSource, SourceNetwork.toReactionNetwork, hx] at h
  let r : Fin 5 := (κ.assign x).1
  have hr : (κ.assign x).1 = r := rfl
  clear_value r
  fin_cases r
  all_goals rw [hr] at h ⊢
  all_goals norm_num at h
  all_goals simp_all

theorem parameterRichCounterexample_assign_one
    (κ : ChildSelection parameterRichCounterexampleSource) (x : κ.species)
    (hx : x.1 = 1) : (κ.assign x).1 = 1 := by
  have h := κ.reactant_match x
  simp [parameterRichCounterexampleSource, SourceNetwork.toReactionNetwork, hx] at h
  let r : Fin 5 := (κ.assign x).1
  have hr : (κ.assign x).1 = r := rfl
  clear_value r
  fin_cases r
  all_goals rw [hr] at h ⊢
  all_goals norm_num at h
  all_goals simp_all

theorem parameterRichCounterexample_assign_two
    (κ : ChildSelection parameterRichCounterexampleSource) (x : κ.species)
    (hx : x.1 = 2) : (κ.assign x).1 = 1 ∨ (κ.assign x).1 = 2 := by
  have h := κ.reactant_match x
  simp [parameterRichCounterexampleSource, SourceNetwork.toReactionNetwork, hx] at h
  let r : Fin 5 := (κ.assign x).1
  have hr : (κ.assign x).1 = r := rfl
  clear_value r
  fin_cases r
  all_goals rw [hr] at h ⊢
  all_goals norm_num at h
  all_goals simp_all

theorem parameterRichCounterexample_assign_three
    (κ : ChildSelection parameterRichCounterexampleSource) (x : κ.species)
    (hx : x.1 = 3) : (κ.assign x).1 = 0 ∨ (κ.assign x).1 = 3 := by
  have h := κ.reactant_match x
  simp [parameterRichCounterexampleSource, SourceNetwork.toReactionNetwork, hx] at h
  let r : Fin 5 := (κ.assign x).1
  have hr : (κ.assign x).1 = r := rfl
  clear_value r
  fin_cases r
  all_goals rw [hr] at h ⊢
  all_goals norm_num at h
  all_goals simp_all

def parameterRichCounterexampleUses21
    (κ : ChildSelection parameterRichCounterexampleSource) : Prop :=
  ∃ x : κ.species, x.1 = 2 ∧ (κ.assign x).1 = 1

def parameterRichCounterexampleUses30
    (κ : ChildSelection parameterRichCounterexampleSource) : Prop :=
  ∃ x : κ.species, x.1 = 3 ∧ (κ.assign x).1 = 0

theorem parameterRichCounterexample_assign_two_of_not_uses21
    (κ : ChildSelection parameterRichCounterexampleSource)
    (hnot : ¬ parameterRichCounterexampleUses21 κ)
    (x : κ.species) (hx : x.1 = 2) : (κ.assign x).1 = 2 := by
  rcases parameterRichCounterexample_assign_two κ x hx with h | h
  · exact False.elim (hnot ⟨x, hx, h⟩)
  · exact h

theorem parameterRichCounterexample_assign_three_of_not_uses30
    (κ : ChildSelection parameterRichCounterexampleSource)
    (hnot : ¬ parameterRichCounterexampleUses30 κ)
    (x : κ.species) (hx : x.1 = 3) : (κ.assign x).1 = 3 := by
  rcases parameterRichCounterexample_assign_three κ x hx with h | h
  · exact False.elim (hnot ⟨x, hx, h⟩)
  · exact h

theorem childSelection_assign_val_ne_of_species_val_ne
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} (κ : ChildSelection Q)
    (x y : κ.species) (hxy : x.1 ≠ y.1) :
    (κ.assign x).1 ≠ (κ.assign y).1 := by
  intro ha
  have hsub : κ.assign x = κ.assign y := Subtype.ext ha
  exact hxy (congrArg Subtype.val (κ.assign.injective hsub))

theorem child_restricts_indexedMatching_of_edge_indices
    (κ : ChildSelection parameterRichCounterexampleSource)
    (E : AutocatalyticCS.IndexedMatching
      parameterRichCounterexampleSource.toReactionNetwork)
    (hedges : ∀ x : κ.species, ∃ i : Fin E.card,
      E.left i = x.1 ∧ E.right i = (κ.assign x).1) :
    κ.Restricts E.toChildSelection := by
  apply childSelection_restricts_of_species_assign
  · intro s hs
    obtain ⟨i, hi, -⟩ := hedges ⟨s, hs⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  · intro x y hxy
    obtain ⟨i, hleft, hright⟩ := hedges x
    have hy : E.indexSpeciesEquiv i = y := by
      apply Subtype.ext
      rw [indexedMatching_indexSpeciesEquiv_val, hleft, hxy]
    rw [← hy, E.toChildSelection_assign_indexSpeciesEquiv]
    exact hright.symm

theorem dNonUnstable_of_restricts_same_species
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {small large : ChildSelection Q}
    (h : small.Restricts large) (hback : large.species ⊆ small.species)
    (hlarge : DNonUnstable large.realMatrix) :
    DNonUnstable small.realMatrix := by
  let f := childRestrictionEmbedding h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hv : (f x).1 = (f y).1 :=
        congrArg (fun z : large.species => z.1) hxy
      exact Subtype.ext hv
    · intro y
      exact ⟨⟨y.1, hback y.2⟩, Subtype.ext rfl⟩
  let e : small.species ≃ large.species := Equiv.ofBijective f hf
  have hmatrix : small.realMatrix = Matrix.reindex e.symm e.symm large.realMatrix := by
    rw [child_realMatrix_eq_restriction h]
    rfl
  rw [hmatrix]
  exact (dNonUnstable_reindex_iff e.symm large.realMatrix).mpr hlarge

theorem parameterRichCounterexample_all_children_dNonUnstable
    (κ : ChildSelection parameterRichCounterexampleSource) :
    DNonUnstable κ.realMatrix := by
  classical
  by_cases h21 : parameterRichCounterexampleUses21 κ
  · obtain ⟨x2, hx2, ha2⟩ := h21
    by_cases h30 : parameterRichCounterexampleUses30 κ
    · obtain ⟨x3, hx3, ha3⟩ := h30
      have hrest : κ.Restricts parameterRichCounterexampleMatching2.toChildSelection :=
        child_restricts_indexedMatching_of_edge_indices κ
          parameterRichCounterexampleMatching2 (by
            intro x
            have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
            rcases hxv with hx | hx | hx | hx
            · have ha := parameterRichCounterexample_assign_zero κ x hx
              exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                κ x x3 (by omega)) (ha.trans ha3.symm))
            · have ha := parameterRichCounterexample_assign_one κ x hx
              exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                κ x x2 (by omega)) (ha.trans ha2.symm))
            · have hxx : x = x2 := Subtype.ext (hx.trans hx2.symm)
              subst x
              refine ⟨0, ?_, ?_⟩ <;>
                simp [parameterRichCounterexampleMatching2, hx2, ha2]
            · have hxx : x = x3 := Subtype.ext (hx.trans hx3.symm)
              subst x
              refine ⟨1, ?_, ?_⟩ <;>
                simp [parameterRichCounterexampleMatching2, hx3, ha3])
      exact dNonUnstable_of_restricts_psd hrest _
        parameterRichCounterexampleMatching2_weight_pos
        parameterRichCounterexampleMatching2_psd
    · have hrest : κ.Restricts parameterRichCounterexampleMatching3a.toChildSelection :=
        child_restricts_indexedMatching_of_edge_indices κ
          parameterRichCounterexampleMatching3a (by
            intro x
            have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
            rcases hxv with hx | hx | hx | hx
            · refine ⟨0, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching3a, hx]
              · simpa [parameterRichCounterexampleMatching3a] using
                  (parameterRichCounterexample_assign_zero κ x hx).symm
            · have ha := parameterRichCounterexample_assign_one κ x hx
              exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                κ x x2 (by omega)) (ha.trans ha2.symm))
            · have hxx : x = x2 := Subtype.ext (hx.trans hx2.symm)
              subst x
              refine ⟨1, ?_, ?_⟩ <;>
                simp [parameterRichCounterexampleMatching3a, hx2, ha2]
            · have ha := parameterRichCounterexample_assign_three_of_not_uses30 κ h30 x hx
              refine ⟨2, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching3a, hx]
              · simpa [parameterRichCounterexampleMatching3a] using ha.symm)
      exact dNonUnstable_of_restricts_psd hrest _
        parameterRichCounterexampleMatching3a_weight_pos
        parameterRichCounterexampleMatching3a_psd
  · by_cases h30 : parameterRichCounterexampleUses30 κ
    · obtain ⟨x3, hx3, ha3⟩ := h30
      have hrest3b : κ.Restricts parameterRichCounterexampleMatching3b.toChildSelection :=
        child_restricts_indexedMatching_of_edge_indices κ
          parameterRichCounterexampleMatching3b (by
            intro x
            have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
            rcases hxv with hx | hx | hx | hx
            · have ha := parameterRichCounterexample_assign_zero κ x hx
              exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                κ x x3 (by omega)) (ha.trans ha3.symm))
            · refine ⟨0, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching3b, hx]
              · simpa [parameterRichCounterexampleMatching3b] using
                  (parameterRichCounterexample_assign_one κ x hx).symm
            · refine ⟨1, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching3b, hx]
              · simpa [parameterRichCounterexampleMatching3b] using
                  (parameterRichCounterexample_assign_two_of_not_uses21 κ h21 x hx).symm
            · have hxx : x = x3 := Subtype.ext (hx.trans hx3.symm)
              subst x
              refine ⟨2, ?_, ?_⟩ <;>
                simp [parameterRichCounterexampleMatching3b, hx3, ha3])
      by_cases hmem1 : (1 : Fin 4) ∈ κ.species
      · by_cases hmem2 : (2 : Fin 4) ∈ κ.species
        · apply dNonUnstable_of_restricts_same_species hrest3b
            (fun s hs => ?_) parameterRichCounterexampleMatching3b_dNonUnstable
          fin_cases s
          · exact False.elim
              ((by decide : (0 : Fin 4) ∉
                parameterRichCounterexampleMatching3b.toChildSelection.species) hs)
          · exact hmem1
          · exact hmem2
          · simpa [hx3] using x3.2
        · have hrest : κ.Restricts parameterRichCounterexampleMatching13.toChildSelection :=
            child_restricts_indexedMatching_of_edge_indices κ
              parameterRichCounterexampleMatching13 (by
                intro x
                have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
                rcases hxv with hx | hx | hx | hx
                · have ha := parameterRichCounterexample_assign_zero κ x hx
                  exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                    κ x x3 (by omega)) (ha.trans ha3.symm))
                · refine ⟨0, ?_, ?_⟩
                  · simp [parameterRichCounterexampleMatching13, hx]
                  · simpa [parameterRichCounterexampleMatching13] using
                      (parameterRichCounterexample_assign_one κ x hx).symm
                · exact False.elim (hmem2 (by simpa [hx] using x.2))
                · have hxx : x = x3 := Subtype.ext (hx.trans hx3.symm)
                  subst x
                  refine ⟨1, ?_, ?_⟩ <;>
                    simp [parameterRichCounterexampleMatching13, hx3, ha3])
          exact dNonUnstable_of_restricts_psd hrest _
            parameterRichCounterexampleMatching13_weight_pos
            parameterRichCounterexampleMatching13_psd
      · have hrest : κ.Restricts parameterRichCounterexampleMatching23.toChildSelection :=
          child_restricts_indexedMatching_of_edge_indices κ
            parameterRichCounterexampleMatching23 (by
              intro x
              have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
              rcases hxv with hx | hx | hx | hx
              · have ha := parameterRichCounterexample_assign_zero κ x hx
                exact False.elim ((childSelection_assign_val_ne_of_species_val_ne
                  κ x x3 (by omega)) (ha.trans ha3.symm))
              · exact False.elim (hmem1 (by simpa [hx] using x.2))
              · refine ⟨0, ?_, ?_⟩
                · simp [parameterRichCounterexampleMatching23, hx]
                · simpa [parameterRichCounterexampleMatching23] using
                    (parameterRichCounterexample_assign_two_of_not_uses21 κ h21 x hx).symm
              · have hxx : x = x3 := Subtype.ext (hx.trans hx3.symm)
                subst x
                refine ⟨1, ?_, ?_⟩ <;>
                  simp [parameterRichCounterexampleMatching23, hx3, ha3])
        exact dNonUnstable_of_restricts_psd hrest _
          parameterRichCounterexampleMatching23_weight_pos
          parameterRichCounterexampleMatching23_psd
    · have hrest : κ.Restricts parameterRichCounterexampleMatching4.toChildSelection :=
        child_restricts_indexedMatching_of_edge_indices κ
          parameterRichCounterexampleMatching4 (by
            intro x
            have hxv : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 := by omega
            rcases hxv with hx | hx | hx | hx
            · refine ⟨0, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching4, hx]
              · simpa [parameterRichCounterexampleMatching4] using
                  (parameterRichCounterexample_assign_zero κ x hx).symm
            · refine ⟨1, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching4, hx]
              · simpa [parameterRichCounterexampleMatching4] using
                  (parameterRichCounterexample_assign_one κ x hx).symm
            · refine ⟨2, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching4, hx]
              · simpa [parameterRichCounterexampleMatching4] using
                  (parameterRichCounterexample_assign_two_of_not_uses21 κ h21 x hx).symm
            · refine ⟨3, ?_, ?_⟩
              · simp [parameterRichCounterexampleMatching4, hx]
              · simpa [parameterRichCounterexampleMatching4] using
                  (parameterRichCounterexample_assign_three_of_not_uses30 κ h30 x hx).symm)
      exact dNonUnstable_of_restricts_psd hrest _
        parameterRichCounterexampleMatching4_weight_pos
        parameterRichCounterexampleMatching4_psd

noncomputable abbrev parameterRichCounterexampleE : ℝ :=
  5187522222797 / 46658000000

noncomputable abbrev parameterRichCounterexampleF : ℝ :=
  28200219703 / 46658000000

noncomputable def parameterRichCounterexampleReactivity :
    Reactivity parameterRichCounterexampleSource where
  value := !![1, 0, 0, parameterRichCounterexampleE;
              0, 1/50, 1/1000, 0;
              0, 0, 5/11, 0;
              0, 0, 0, parameterRichCounterexampleF;
              0, 0, 0, 0]
  nonneg := by
    intro r s
    fin_cases r <;> fin_cases s <;>
      norm_num [parameterRichCounterexampleE, parameterRichCounterexampleF]
  positive_of_reactant := by
    intro r s h
    fin_cases r <;> fin_cases s <;>
      simp_all [SourceNetwork.Reactant, parameterRichCounterexampleSource,
        parameterRichCounterexampleE, parameterRichCounterexampleF]
  zero_of_not_reactant := by
    intro r s h
    fin_cases r <;> fin_cases s <;>
      simp [SourceNetwork.Reactant, parameterRichCounterexampleSource] at h ⊢

noncomputable def parameterRichCounterexampleJacobian : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0,
      -parameterRichCounterexampleE + parameterRichCounterexampleF;
     0, -4/50, -4/1000, 6*parameterRichCounterexampleF;
     4, -2/50, -2/1000-20/11,
      4*parameterRichCounterexampleE + parameterRichCounterexampleF;
     -2, 0, 10/11,
      -2*parameterRichCounterexampleE-2*parameterRichCounterexampleF]

theorem parameterRichCounterexample_jacobian_eq :
    parameterRichCounterexampleSource.jacobian
        parameterRichCounterexampleReactivity =
      parameterRichCounterexampleJacobian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNetwork.jacobian, SourceNetwork.stoich,
      parameterRichCounterexampleSource,
      parameterRichCounterexampleReactivity,
      parameterRichCounterexampleJacobian,
      parameterRichCounterexampleE, parameterRichCounterexampleF,
      Fin.sum_univ_succ]
  all_goals norm_num

noncomputable def parameterRichCounterexampleRoot : ℂ :=
  (1 / 500 : ℝ) + (51 / 500 : ℝ) * Complex.I

theorem parameterRichCounterexample_root_re_pos :
    0 < parameterRichCounterexampleRoot.re := by
  norm_num [parameterRichCounterexampleRoot]

noncomputable def parameterRichCounterexampleEigenvector : Fin 4 → ℂ :=
  ![(-152886431705 : ℂ) + 15563289455 * Complex.I,
    (23331004034 : ℂ) - 30699360512 * Complex.I,
    (7890610882 : ℂ) + 34396287629 * Complex.I,
    (1399740000 : ℂ)]

theorem parameterRichCounterexample_eigenpair :
    HasEigenpair parameterRichCounterexampleJacobian
      parameterRichCounterexampleRoot
      parameterRichCounterexampleEigenvector := by
  constructor
  · intro hzero
    have h3 := congrFun hzero (3 : Fin 4)
    have hre := congrArg Complex.re h3
    simp [parameterRichCounterexampleEigenvector] at hre
  · intro i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, complexify,
        parameterRichCounterexampleJacobian,
        parameterRichCounterexampleRoot,
        parameterRichCounterexampleEigenvector,
        parameterRichCounterexampleE, parameterRichCounterexampleF]
    all_goals ring_nf
    all_goals rw [Complex.I_sq]
    all_goals ring

theorem parameterRichCounterexample_hurwitzUnstable :
    HurwitzUnstable
      (parameterRichCounterexampleSource.jacobian
        parameterRichCounterexampleReactivity) := by
  rw [parameterRichCounterexample_jacobian_eq]
  exact ⟨parameterRichCounterexampleRoot,
    parameterRichCounterexampleEigenvector,
    parameterRichCounterexample_root_re_pos,
    parameterRichCounterexample_eigenpair⟩

theorem parameterRichCounterexample_no_dUnstableCore :
    ¬ ∃ core : ChildSelection parameterRichCounterexampleSource,
      IsDUnstableCore core := by
  rintro ⟨core, hcore⟩
  obtain ⟨d, hd, hunstable⟩ := hcore.1
  exact parameterRichCounterexample_all_children_dNonUnstable core d hd hunstable

/-- Exact literature-scoped counterexample: the source is consistent, its
admissible parameter-rich Jacobian is strictly unstable, and every supported
child is D-nonunstable. -/
theorem parameterRich_consistent_counterexample :
    parameterRichCounterexampleSource.Consistent ∧
      HurwitzUnstable
        (parameterRichCounterexampleSource.jacobian
          parameterRichCounterexampleReactivity) ∧
      ∀ child : ChildSelection parameterRichCounterexampleSource,
        DNonUnstable child.realMatrix :=
  ⟨parameterRichCounterexampleSource_consistent,
    parameterRichCounterexample_hurwitzUnstable,
    parameterRichCounterexample_all_children_dNonUnstable⟩

/-- Exact source-faithful refutation: a consistent source has an admissible
parameter-rich Jacobian that is strictly unstable although none of its
supported children is D-unstable. -/
theorem parameterRichCounterexample_refutes_core_necessity :
    parameterRichCounterexampleSource.Consistent ∧
      HurwitzUnstable
        (parameterRichCounterexampleSource.jacobian
          parameterRichCounterexampleReactivity) ∧
      ¬ ∃ core : ChildSelection parameterRichCounterexampleSource,
        IsDUnstableCore core :=
  ⟨parameterRichCounterexampleSource_consistent,
    parameterRichCounterexample_hurwitzUnstable,
    parameterRichCounterexample_no_dUnstableCore⟩

/-- Consequently, the consistency-scoped necessity statement already fails
for four species and five reactions. -/
theorem parameterRich_consistent_core_necessity_fin4_fin5_false :
    ¬ (∀ (Q : SourceNetwork (Fin 4) (Fin 5)), Q.Consistent →
      ∀ R : Reactivity Q, HurwitzUnstable (Q.jacobian R) →
        ∃ core : ChildSelection Q, IsDUnstableCore core) := by
  intro h
  exact parameterRichCounterexample_no_dUnstableCore
    (h parameterRichCounterexampleSource
      parameterRichCounterexampleSource_consistent
      parameterRichCounterexampleReactivity
      parameterRichCounterexample_hurwitzUnstable)

end DUnstableCores
