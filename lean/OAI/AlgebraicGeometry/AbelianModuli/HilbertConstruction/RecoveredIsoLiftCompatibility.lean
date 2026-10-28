import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLift

/-! # Recovered Iso Lift Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLiftCompatibility

noncomputable section

/-! The lifted Cartesian recovery commutes with the prescribed morphism into the ambient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem recoveredIsoLift_comp
    {S T : Scheme.{u}} (r : T ⟶ S) {A : Over T} {X Y : Over S}
    (i : Y ⟶ X) [IsIso ((Over.pullback r).map i)]
    (q : A.left ⟶ X.left) (h : IsPullback q A.hom X.hom r) :
    RecoveredIsoLift.recoveredIsoLift r i q h ≫ i.left = q := by
  let e : A.left ⟶ pullback X.hom r := h.isoPullback.hom
  let v : pullback X.hom r ⟶ pullback Y.hom r := (asIso ((Over.pullback r).map i)).inv.left
  let f : pullback Y.hom r ⟶ pullback X.hom r := ((Over.pullback r).map i).left
  let j : Y.left ⟶ X.left := i.left
  have hv : v ≫ f = 𝟙 (pullback X.hom r) :=
    congrArg (fun k => k.left) (asIso ((Over.pullback r).map i)).inv_hom_id
  have hf : f ≫ pullback.fst X.hom r = pullback.fst Y.hom r ≫ j :=
    (Projective.PresentationBaseChange.overPullback_map_isPullback i r).w.symm
  have he : e ≫ pullback.fst X.hom r = q := h.isoPullback_hom_fst
  change ((e ≫ v) ≫ pullback.fst Y.hom r) ≫ j = q
  rw [Category.assoc, ← hf, ← Category.assoc, Category.assoc e v f, hv, Category.comp_id, he]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLiftCompatibility
