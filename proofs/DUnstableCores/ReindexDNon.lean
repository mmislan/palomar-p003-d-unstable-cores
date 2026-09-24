import proofs.DUnstableCores.EigenpairFromRoot

/-!
# Reindexing invariance of open-half-plane and D-instability

The child-selection matrices naturally live on subtype indices.  These lemmas
transport the spectral predicates across an equivalence of finite index types.
-/

namespace DUnstableCores

theorem hurwitzUnstable_reindex_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) :
    HurwitzUnstable (Matrix.reindex e e A) ↔ HurwitzUnstable A := by
  classical
  constructor
  · rintro ⟨lam, v, hlam, heig⟩
    have hroot := heig.isRoot_charpoly
    have hchar : (complexify (Matrix.reindex e e A)).charpoly =
        (complexify A).charpoly := by
      have hmatrix : complexify (Matrix.reindex e e A) =
          Matrix.reindex e e (complexify A) := by
        ext i j
        rfl
      rw [hmatrix]
      exact Matrix.charpoly_reindex e (complexify A)
    rw [hchar] at hroot
    obtain ⟨w, hw⟩ := hasEigenpair_of_isRoot_complexified_charpoly hroot
    exact ⟨lam, w, hlam, hw⟩
  · rintro ⟨lam, v, hlam, heig⟩
    have hroot := heig.isRoot_charpoly
    have hchar : (complexify (Matrix.reindex e e A)).charpoly =
        (complexify A).charpoly := by
      have hmatrix : complexify (Matrix.reindex e e A) =
          Matrix.reindex e e (complexify A) := by
        ext i j
        rfl
      rw [hmatrix]
      exact Matrix.charpoly_reindex e (complexify A)
    have hroot' : (complexify (Matrix.reindex e e A)).charpoly.IsRoot lam := by
      rw [hchar]
      exact hroot
    obtain ⟨w, hw⟩ := hasEigenpair_of_isRoot_complexified_charpoly hroot'
    exact ⟨lam, w, hlam, hw⟩

theorem dNonUnstable_reindex_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) :
    DNonUnstable (Matrix.reindex e e A) ↔ DNonUnstable A := by
  constructor
  · intro h d hd hunstable
    let d' : κ → ℝ := fun k => d (e.symm k)
    have hd' : ∀ k, 0 < d' k := fun k => hd (e.symm k)
    have hscale : rightScale A d = Matrix.reindex e.symm e.symm
        (rightScale (Matrix.reindex e e A) d') := by
      ext i j
      simp [rightScale, d']
    apply h d' hd'
    rw [hscale] at hunstable
    exact (hurwitzUnstable_reindex_iff e.symm _).mp hunstable
  · intro h d hd hunstable
    let d' : ι → ℝ := fun i => d (e i)
    have hd' : ∀ i, 0 < d' i := fun i => hd (e i)
    have hscale : rightScale (Matrix.reindex e e A) d =
        Matrix.reindex e e (rightScale A d') := by
      ext i j
      simp [rightScale, d']
    apply h d' hd'
    rw [hscale] at hunstable
    exact (hurwitzUnstable_reindex_iff e _).mp hunstable

end DUnstableCores
