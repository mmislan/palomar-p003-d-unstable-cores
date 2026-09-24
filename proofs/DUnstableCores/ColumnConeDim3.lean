import proofs.DUnstableCores.RouthHurwitzDim3

/-!
# Scalar core of the cubic one-column cone argument

After two columns and their scalings are fixed, the second cubic
Routh--Hurwitz determinant is a quadratic in the scaling of the remaining
column.  The lemma below proves directly, without a square-root or strict
stability assumption, that nonnegativity of the two endpoint quadratics is
preserved by a positive mixture of their column data.
-/

namespace DUnstableCores

/-- If a linear polynomial with nonnegative constant term is nonnegative at
every positive argument, then its slope is nonnegative. -/
theorem slope_nonneg_of_linear_nonneg_on_pos
    (P L : ℝ) (hP : 0 ≤ P)
    (h : ∀ s : ℝ, 0 < s → 0 ≤ P + s * L) :
    0 ≤ L := by
  by_contra hnot
  have hL : L < 0 := lt_of_not_ge hnot
  have hden : 0 < -L := neg_pos.mpr hL
  have hnum : 0 < P + 1 := by linarith
  let s : ℝ := (P + 1) / (-L)
  have hs : 0 < s := div_pos hnum hden
  have hsL : s * L = -(P + 1) := by
    have hdenne : -L ≠ 0 := ne_of_gt hden
    calc
      s * L = -(s * (-L)) := by ring
      _ = -(P + 1) := by rw [show s * (-L) = P + 1 by
        exact div_mul_cancel₀ (P + 1) hdenne]
  have hvalue := h s hs
  rw [hsL] at hvalue
  linarith

/-- An affine function nonnegative on the open positive ray has both
nonnegative intercept and nonnegative slope.  This boundary lemma avoids any
appeal to limits when a column scaling tends to zero or infinity. -/
theorem intercept_slope_nonneg_of_affine_nonneg_on_pos
    (P L : ℝ) (h : ∀ s : ℝ, 0 < s → 0 ≤ P + s * L) :
    0 ≤ P ∧ 0 ≤ L := by
  have hP : 0 ≤ P := by
    by_cases hL : 0 ≤ L
    · by_contra hPnot
      have hPneg : P < 0 := lt_of_not_ge hPnot
      have hden : 0 < L + 1 := by linarith
      let s : ℝ := (-P) / (L + 1)
      have hs : 0 < s := div_pos (neg_pos.mpr hPneg) hden
      have hsprod : s * (L + 1) = -P := by
        exact div_mul_cancel₀ (-P) (ne_of_gt hden)
      have hvalue := h s hs
      have hmul : 0 ≤ (P + s * L) * (L + 1) :=
        mul_nonneg hvalue hden.le
      have hid : (P + s * L) * (L + 1) = P := by
        calc
          (P + s * L) * (L + 1) = P * (L + 1) + L * (s * (L + 1)) := by ring
          _ = P := by rw [hsprod]; ring
      rw [hid] at hmul
      exact hPnot hmul
    · have hLneg : L < 0 := lt_of_not_ge hL
      have hvalue := h 1 (by norm_num)
      linarith
  exact ⟨hP, slope_nonneg_of_linear_nonneg_on_pos P L hP h⟩

/-- Algebraic one-column mixture lemma for the cubic determinant.

`P + s*Lᵢ + s²*xᵢ*yᵢ` is the endpoint `Delta_2` polynomial.  The mixed
column has linear data `L₁+t*L₂`, `x₁+t*x₂`, and `y₁+t*y₂`. -/
theorem cubic_quadratic_mixture_nonneg
    (P L₁ L₂ x₁ x₂ y₁ y₂ t : ℝ)
    (hP : 0 ≤ P)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (ht : 0 ≤ t)
    (h₁ : ∀ s : ℝ, 0 < s →
      0 ≤ P + s * L₁ + s ^ 2 * x₁ * y₁)
    (h₂ : ∀ s : ℝ, 0 < s →
      0 ≤ P + s * L₂ + s ^ 2 * x₂ * y₂) :
    ∀ s : ℝ, 0 < s →
      0 ≤ P + s * (L₁ + t * L₂) +
        s ^ 2 * (x₁ + t * x₂) * (y₁ + t * y₂) := by
  intro s hs
  by_cases hx₁zero : x₁ = 0
  · have hL₁ : 0 ≤ L₁ := by
      apply slope_nonneg_of_linear_nonneg_on_pos P L₁ hP
      intro r hr
      simpa [hx₁zero] using h₁ r hr
    by_cases hx₂zero : x₂ = 0
    · have hL₂ : 0 ≤ L₂ := by
        apply slope_nonneg_of_linear_nonneg_on_pos P L₂ hP
        intro r hr
        simpa [hx₂zero] using h₂ r hr
      have hlin := add_nonneg hP
        (mul_nonneg hs.le (add_nonneg hL₁ (mul_nonneg ht hL₂)))
      simpa [hx₁zero, hx₂zero] using hlin
    · have hx₂pos : 0 < x₂ := lt_of_le_of_ne hx₂ (Ne.symm hx₂zero)
      by_cases htzero : t = 0
      · simpa [htzero] using h₁ s hs
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
        have h₂value := h₂ (t * s) (mul_pos htpos hs)
        have hcross : 0 ≤ s ^ 2 * (t * x₂) * y₁ := by positivity
        have hidentity :
            P + s * (L₁ + t * L₂) +
                s ^ 2 * (x₁ + t * x₂) * (y₁ + t * y₂) =
              (P + (t * s) * L₂ + (t * s) ^ 2 * x₂ * y₂) +
                s * L₁ + s ^ 2 * (t * x₂) * y₁ := by
          rw [hx₁zero]
          ring
        rw [hidentity]
        exact add_nonneg (add_nonneg h₂value (mul_nonneg hs.le hL₁)) hcross
  · have hx₁pos : 0 < x₁ := lt_of_le_of_ne hx₁ (Ne.symm hx₁zero)
    by_cases hx₂zero : x₂ = 0
    · have hL₂ : 0 ≤ L₂ := by
        apply slope_nonneg_of_linear_nonneg_on_pos P L₂ hP
        intro r hr
        simpa [hx₂zero] using h₂ r hr
      have h₁value := h₁ s hs
      have hcross : 0 ≤ s ^ 2 * x₁ * (t * y₂) := by positivity
      have hidentity :
          P + s * (L₁ + t * L₂) +
              s ^ 2 * (x₁ + t * x₂) * (y₁ + t * y₂) =
            (P + s * L₁ + s ^ 2 * x₁ * y₁) +
              s * (t * L₂) + s ^ 2 * x₁ * (t * y₂) := by
        rw [hx₂zero]
        ring
      rw [hidentity]
      exact add_nonneg
        (add_nonneg h₁value (mul_nonneg hs.le (mul_nonneg ht hL₂))) hcross
    · have hx₂pos : 0 < x₂ := lt_of_le_of_ne hx₂ (Ne.symm hx₂zero)
      let X : ℝ := x₁ + t * x₂
      have hX : 0 < X := by dsimp [X]; positivity
      have hr₁ : 0 < s * X / x₁ := div_pos (mul_pos hs hX) hx₁pos
      have hr₂ : 0 < s * X / x₂ := div_pos (mul_pos hs hX) hx₂pos
      have h₁value := h₁ (s * X / x₁) hr₁
      have h₂value := h₂ (s * X / x₂) hr₂
      have hweighted :
          0 ≤ x₁ * (P + (s * X / x₁) * L₁ +
              (s * X / x₁) ^ 2 * x₁ * y₁) +
            t * x₂ * (P + (s * X / x₂) * L₂ +
              (s * X / x₂) ^ 2 * x₂ * y₂) :=
        add_nonneg (mul_nonneg hx₁ h₁value)
          (mul_nonneg (mul_nonneg ht hx₂) h₂value)
      have hidentity :
          x₁ * (P + (s * X / x₁) * L₁ +
              (s * X / x₁) ^ 2 * x₁ * y₁) +
            t * x₂ * (P + (s * X / x₂) * L₂ +
              (s * X / x₂) ^ 2 * x₂ * y₂) =
          X * (P + s * (L₁ + t * L₂) +
            s ^ 2 * (x₁ + t * x₂) * (y₁ + t * y₂)) := by
        dsimp [X]
        field_simp
        ring
      rw [hidentity] at hweighted
      exact nonneg_of_mul_nonneg_right hweighted hX

end DUnstableCores
