import proofs.DUnstableCores.ColumnConeDim3

/-!
# Explicit cubic coefficient exporter

This file exposes the three lower characteristic coefficients of a `3 x 3`
matrix in a form adapted to column mixtures.  The formulas are proved from
the literal determinant, so later source-level arguments need not depend on
opaque characteristic-polynomial simplification.
-/

namespace DUnstableCores

open Polynomial

def cubicCoeff1 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -(A 0 0 + A 1 1 + A 2 2)

def cubicCoeff2 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0 +
  A 0 0 * A 2 2 - A 0 2 * A 2 0 +
  A 1 1 * A 2 2 - A 1 2 * A 2 1

def cubicCoeff3 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -Matrix.det A

/-- Literal characteristic polynomial of a real `3 x 3` matrix. -/
theorem isCubicCharpoly_explicit (A : Matrix (Fin 3) (Fin 3) ℝ) :
    IsCubicCharpoly A (cubicCoeff1 A) (cubicCoeff2 A) (cubicCoeff3 A) := by
  unfold IsCubicCharpoly Matrix.charpoly Matrix.charmatrix
    cubicCoeff1 cubicCoeff2 cubicCoeff3
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp
  ring

def fromColumns (c0 c1 c2 : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![c0 i, c1 i, c2 i] j

def scaledColumns (c0 c1 c2 : Fin 3 → ℝ) (d0 d1 d2 : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fromColumns (fun i => c0 i * d0) (fun i => c1 i * d1)
    (fun i => c2 i * d2)

theorem cubicCoeff1_scaledColumns
    (c0 c1 c2 : Fin 3 → ℝ) (d0 d1 d2 : ℝ) :
    cubicCoeff1 (scaledColumns c0 c1 c2 d0 d1 d2) =
      -(c0 0 * d0 + c1 1 * d1) + d2 * (-c2 2) := by
  simp [cubicCoeff1, scaledColumns, fromColumns]
  ring

theorem cubicCoeff2_scaledColumns
    (c0 c1 c2 : Fin 3 → ℝ) (d0 d1 d2 : ℝ) :
    cubicCoeff2 (scaledColumns c0 c1 c2 d0 d1 d2) =
      d0 * d1 * (c0 0 * c1 1 - c1 0 * c0 1) +
      d2 * (d0 * (c0 0 * c2 2 - c2 0 * c0 2) +
        d1 * (c1 1 * c2 2 - c2 1 * c1 2)) := by
  simp [cubicCoeff2, scaledColumns, fromColumns]
  ring

theorem cubicCoeff3_scaledColumns
    (c0 c1 c2 : Fin 3 → ℝ) (d0 d1 d2 : ℝ) :
    cubicCoeff3 (scaledColumns c0 c1 c2 d0 d1 d2) =
      d2 * (-(d0 * d1 * Matrix.det (fromColumns c0 c1 c2))) := by
  simp [cubicCoeff3, scaledColumns, fromColumns, Matrix.det_fin_three]
  ring

/-- The scaled-column constructor is the ordinary right diagonal scaling of
the unscaled column matrix. -/
theorem scaledColumns_eq_rightScale
    (c0 c1 c2 : Fin 3 → ℝ) (d0 d1 d2 : ℝ) :
    scaledColumns c0 c1 c2 d0 d1 d2 =
      rightScale (fromColumns c0 c1 c2) ![d0, d1, d2] := by
  ext i j
  fin_cases j <;> simp [scaledColumns, fromColumns, rightScale]

/-- A coefficient-level certificate quantified over all positive column
scalings.  This is the convenient finite-dimensional interface for column
mixtures. -/
def CubicColumnCertificate (c0 c1 c2 : Fin 3 → ℝ) : Prop :=
  ∀ d0 d1 d2 : ℝ, 0 < d0 → 0 < d1 → 0 < d2 →
    let A := scaledColumns c0 c1 c2 d0 d1 d2
    0 ≤ cubicCoeff1 A ∧ 0 ≤ cubicCoeff2 A ∧ 0 ≤ cubicCoeff3 A ∧
      0 ≤ cubicCoeff1 A * cubicCoeff2 A - cubicCoeff3 A

/-- The coefficient certificate implies the campaign's boundary-permitting
universal D-non-instability predicate. -/
theorem CubicColumnCertificate.dNonUnstable
    {c0 c1 c2 : Fin 3 → ℝ} (h : CubicColumnCertificate c0 c1 c2) :
    DNonUnstable (fromColumns c0 c1 c2) := by
  intro d hd
  have hc := h (d 0) (d 1) (d 2) (hd 0) (hd 1) (hd 2)
  have hdext : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hdext, ← scaledColumns_eq_rightScale]
  exact hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
    (scaledColumns c0 c1 c2 (d 0) (d 1) (d 2))
    (cubicCoeff1 (scaledColumns c0 c1 c2 (d 0) (d 1) (d 2)))
    (cubicCoeff2 (scaledColumns c0 c1 c2 (d 0) (d 1) (d 2)))
    (cubicCoeff3 (scaledColumns c0 c1 c2 (d 0) (d 1) (d 2)))
    (isCubicCharpoly_explicit _ ) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- Cubic coefficient certificates form a convex cone in any one column when
the other two columns are fixed. -/
theorem cubicColumnCertificate_thirdColumn_add
    {c0 c1 w1 w2 : Fin 3 → ℝ} {t : ℝ}
    (ht : 0 ≤ t)
    (h1 : CubicColumnCertificate c0 c1 w1)
    (h2 : CubicColumnCertificate c0 c1 w2) :
    CubicColumnCertificate c0 c1 (fun i => w1 i + t * w2 i) := by
  unfold CubicColumnCertificate at h1 h2 ⊢
  intro d0 d1 d2 hd0 hd1 hd2
  dsimp only
  let p := -(c0 0 * d0 + c1 1 * d1)
  let q := d0 * d1 * (c0 0 * c1 1 - c1 0 * c0 1)
  let x1 := -w1 2
  let x2 := -w2 2
  let y1 := d0 * (c0 0 * w1 2 - w1 0 * c0 2) +
    d1 * (c1 1 * w1 2 - w1 1 * c1 2)
  let y2 := d0 * (c0 0 * w2 2 - w2 0 * c0 2) +
    d1 * (c1 1 * w2 2 - w2 1 * c1 2)
  let z1 := -(d0 * d1 * Matrix.det (fromColumns c0 c1 w1))
  let z2 := -(d0 * d1 * Matrix.det (fromColumns c0 c1 w2))
  let P := p * q
  let L1 := p * y1 + q * x1 - z1
  let L2 := p * y2 + q * x2 - z2
  have ha1_1 : ∀ r : ℝ, 0 < r → 0 ≤ p + r * x1 := by
    intro r hr
    have hc := (h1 d0 d1 r hd0 hd1 hr).1
    simpa [cubicCoeff1_scaledColumns, p, x1] using hc
  have ha1_2 : ∀ r : ℝ, 0 < r → 0 ≤ p + r * x2 := by
    intro r hr
    have hc := (h2 d0 d1 r hd0 hd1 hr).1
    simpa [cubicCoeff1_scaledColumns, p, x2] using hc
  have ha2_1 : ∀ r : ℝ, 0 < r → 0 ≤ q + r * y1 := by
    intro r hr
    have hc := (h1 d0 d1 r hd0 hd1 hr).2.1
    simpa [cubicCoeff2_scaledColumns, q, y1] using hc
  have ha2_2 : ∀ r : ℝ, 0 < r → 0 ≤ q + r * y2 := by
    intro r hr
    have hc := (h2 d0 d1 r hd0 hd1 hr).2.1
    simpa [cubicCoeff2_scaledColumns, q, y2] using hc
  obtain ⟨hp, hx1⟩ :=
    intercept_slope_nonneg_of_affine_nonneg_on_pos p x1 ha1_1
  obtain ⟨_, hx2⟩ :=
    intercept_slope_nonneg_of_affine_nonneg_on_pos p x2 ha1_2
  obtain ⟨hq, hy1⟩ :=
    intercept_slope_nonneg_of_affine_nonneg_on_pos q y1 ha2_1
  obtain ⟨_, hy2⟩ :=
    intercept_slope_nonneg_of_affine_nonneg_on_pos q y2 ha2_2
  have hz1 : 0 ≤ z1 := by
    have hc := (h1 d0 d1 1 hd0 hd1 (by norm_num)).2.2.1
    simpa [cubicCoeff3_scaledColumns, z1] using hc
  have hz2 : 0 ≤ z2 := by
    have hc := (h2 d0 d1 1 hd0 hd1 (by norm_num)).2.2.1
    simpa [cubicCoeff3_scaledColumns, z2] using hc
  have hdelta1 : ∀ r : ℝ, 0 < r →
      0 ≤ P + r * L1 + r ^ 2 * x1 * y1 := by
    intro r hr
    have hc := (h1 d0 d1 r hd0 hd1 hr).2.2.2
    rw [cubicCoeff1_scaledColumns, cubicCoeff2_scaledColumns,
      cubicCoeff3_scaledColumns] at hc
    dsimp [P, L1, p, q, x1, y1, z1]
    ring_nf at hc ⊢
    exact hc
  have hdelta2 : ∀ r : ℝ, 0 < r →
      0 ≤ P + r * L2 + r ^ 2 * x2 * y2 := by
    intro r hr
    have hc := (h2 d0 d1 r hd0 hd1 hr).2.2.2
    rw [cubicCoeff1_scaledColumns, cubicCoeff2_scaledColumns,
      cubicCoeff3_scaledColumns] at hc
    dsimp [P, L2, p, q, x2, y2, z2]
    ring_nf at hc ⊢
    exact hc
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hmixdelta := cubic_quadratic_mixture_nonneg
    P L1 L2 x1 x2 y1 y2 t hP hx1 hx2 hy1 hy2 ht hdelta1 hdelta2 d2 hd2
  constructor
  · rw [cubicCoeff1_scaledColumns]
    have hnon : 0 ≤ p + d2 * (x1 + t * x2) := by positivity
    convert hnon using 1
    dsimp [p, x1, x2]
    ring
  constructor
  · rw [cubicCoeff2_scaledColumns]
    have hnon : 0 ≤ q + d2 * (y1 + t * y2) := by positivity
    convert hnon using 1
    dsimp [q, y1, y2]
    ring
  constructor
  · have hz : 0 ≤ d2 * (z1 + t * z2) := by positivity
    rw [cubicCoeff3_scaledColumns]
    dsimp [z1, z2] at hz ⊢
    simp [fromColumns, Matrix.det_fin_three] at hz ⊢
    ring_nf at hz ⊢
    linarith
  · rw [cubicCoeff1_scaledColumns, cubicCoeff2_scaledColumns,
      cubicCoeff3_scaledColumns]
    dsimp [P, L1, L2, p, q, x1, x2, y1, y2, z1, z2] at hmixdelta ⊢
    simp [fromColumns, Matrix.det_fin_three] at hmixdelta ⊢
    ring_nf at hmixdelta ⊢
    linarith

end DUnstableCores
