import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction

/-! # Support Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: open restriction retains precisely the generic points lying in the open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]

theorem openSupportPullback_nonempty_generic (W : IrreducibleCloseds Y) :
    Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W) ↔ irreducibleSetEquivPoints W ∈ Set.range i := by
  rw [SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem_open_set_iff i.opensRange.isOpen).mpr
      ⟨i x, hx, x, rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [Set.mem_preimage, hx]
    exact (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem

instance openSupportPoint_nonempty (x : X) :
    Nonempty (SupportRestriction.BundleCycles.openSupportPullback i (irreducibleSetEquivPoints.symm (i x))) :=
  (openSupportPullback_nonempty_generic i _).mpr
    ((irreducibleSetEquivPoints.apply_symm_apply (i x)).symm ▸ ⟨x, rfl⟩)

theorem openRestrictedSupport_pointClosure (x : X) :
    SupportRestriction.BundleCycles.openRestrictedSupport i (irreducibleSetEquivPoints.symm (i x)) = irreducibleSetEquivPoints.symm x := by
  apply IrreducibleCloseds.ext
  rw [SupportRestriction.BundleCycles.openRestrictedSupport_coe]
  change i ⁻¹' closure {i x} = closure {x}
  simpa only [Set.image_singleton] using
    (i.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image {x}).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint.BundleCycles
