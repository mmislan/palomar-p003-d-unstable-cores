import proofs.AutocatalyticCS.SourceSemantics

/-! Shared matching-index helpers, moved verbatim from AlternatingMatchingExchange. -/
namespace AutocatalyticCS.IndexedMatching
variable {X R : Type*} [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

/-- The canonical enumeration of the species endpoint set by matching index. -/
noncomputable def indexSpeciesEquiv (E : IndexedMatching Q) :
    Fin E.card ≃ E.species :=
  Equiv.ofBijective
    (fun i => ⟨E.left i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact E.left_injective (congrArg Subtype.val hij), by
      intro x
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem toChildSelection_assign_indexSpeciesEquiv
    (E : IndexedMatching Q) (i : Fin E.card) :
    (E.toChildSelection.assign (E.indexSpeciesEquiv i)).1 = E.right i := by
  obtain ⟨k, hleft, hright⟩ :=
    E.exists_index_of_species (E.indexSpeciesEquiv i)
  change E.left k = E.left i at hleft
  have hki : k = i := E.left_injective hleft
  subst k
  exact hright.symm

end AutocatalyticCS.IndexedMatching
