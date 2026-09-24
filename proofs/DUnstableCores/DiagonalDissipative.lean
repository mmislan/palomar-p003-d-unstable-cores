import proofs.DUnstableCores.DScaling

/-!
# Diagonal dissipativity and right-scaling non-instability

A nonpositive weighted real quadratic form is preserved by positive right
column scaling after the eigenvector coordinates are rescaled.  This gives a
compact exact certificate for boundary-permitting D-noninstability and is the
energy interface used by the factor-cactus calculation.
-/

namespace DUnstableCores

open scoped BigOperators

/-- One positive diagonal weight makes the real quadratic form of `A`
nonpositive.  Two vectors are included so the certificate applies directly to
the real and imaginary coordinates of a complex eigenvector. -/
def WeightedDissipative {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, 0 < p i) ∧
    ∀ x y : ι → ℝ,
      ∑ i, p i * (x i * A.mulVec x i + y i * A.mulVec y i) ≤ 0

/-- A positive weighted dissipativity certificate rules out every strict
right-half-plane eigenvalue after every positive right diagonal scaling. -/
theorem WeightedDissipative.dNonUnstable
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : WeightedDissipative A p) : DNonUnstable A := by
  classical
  intro d hd hunstable
  obtain ⟨lambda, z, hlambda, hz⟩ := hunstable
  let x : ι → ℝ := fun i => (z i).re
  let y : ι → ℝ := fun i => (z i).im
  let X : ι → ℝ := fun i => d i * x i
  let Y : ι → ℝ := fun i => d i * y i
  have hxEq : ∀ i, A.mulVec X i = lambda.re * x i - lambda.im * y i := by
    intro i
    have hi := hz.2 i
    have hre := congrArg Complex.re hi
    simpa [Matrix.mulVec, dotProduct, complexify, rightScale, x, y, X,
      Complex.mul_re, Complex.mul_im, mul_assoc] using hre
  have hyEq : ∀ i, A.mulVec Y i = lambda.im * x i + lambda.re * y i := by
    intro i
    have hi := hz.2 i
    have him := congrArg Complex.im hi
    simpa [Matrix.mulVec, dotProduct, complexify, rightScale, x, y, Y,
      Complex.mul_re, Complex.mul_im, mul_assoc, add_comm] using him
  have henergy := h.2 X Y
  have hidentity :
      (∑ i, p i * (X i * A.mulVec X i + Y i * A.mulVec Y i)) =
        lambda.re * ∑ i, p i * d i * (x i ^ 2 + y i ^ 2) := by
    calc
      (∑ i, p i * (X i * A.mulVec X i + Y i * A.mulVec Y i)) =
          ∑ i, lambda.re * (p i * d i * (x i ^ 2 + y i ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hxEq i, hyEq i]
            dsimp [X, Y]
            ring
      _ = lambda.re * ∑ i, p i * d i * (x i ^ 2 + y i ^ 2) := by
            rw [Finset.mul_sum]
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hz.1
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hex
  have hxy : 0 < x i ^ 2 + y i ^ 2 := by
    have hn : 0 < Complex.normSq (z i) := Complex.normSq_pos.mpr hi
    simpa [Complex.normSq, x, y, pow_two] using hn
  have hall : ∀ j ∈ Finset.univ,
      0 ≤ p j * d j * (x j ^ 2 + y j ^ 2) := by
    intro j hj
    exact mul_nonneg (mul_nonneg (h.1 j).le (hd j).le)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hterm : 0 < p i * d i * (x i ^ 2 + y i ^ 2) := by
    exact mul_pos (mul_pos (h.1 i) (hd i)) hxy
  have hsum : 0 < ∑ j, p j * d j * (x j ^ 2 + y j ^ 2) :=
    Finset.sum_pos' hall ⟨i, Finset.mem_univ i, hterm⟩
  rw [hidentity] at henergy
  nlinarith

end DUnstableCores
