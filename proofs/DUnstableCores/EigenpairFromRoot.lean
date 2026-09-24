import proofs.DUnstableCores.CharPoly

/-! General spectral helper, moved verbatim from RouthHurwitzDim3. -/
namespace DUnstableCores
open Polynomial

/-- A complex root of the complexified characteristic polynomial supplies a
direct matrix eigenpair witness. -/
theorem hasEigenpair_of_isRoot_complexified_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {lam : ℂ}
    (hroot : (complexify A).charpoly.IsRoot lam) :
    ∃ v : ι → ℂ, HasEigenpair A lam v := by
  classical
  let f : Module.End ℂ (ι → ℂ) := (complexify A).mulVecLin
  have hrootEnd : f.charpoly.IsRoot lam := by
    simpa [f, Matrix.charpoly_mulVecLin] using hroot
  have heigenvalue : Module.End.HasEigenvalue f lam :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lam).mpr hrootEnd
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  intro i
  have happly : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hi := congrFun happly i
  simpa [f, Matrix.mulVecLin_apply] using hi

end DUnstableCores
