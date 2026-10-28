import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductOpen

/-! # Proper Product Open Geometry -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProperProductOpenGeometry.Construction

noncomputable section

/-!
# Completion: the actual pullback square for restriction of a product to an open
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (U : Y.Opens)

/-- Restricting the second factor is the base change of its open immersion. -/
theorem properProductOpen_isPullback :
    IsPullback (ProductOpen.Construction.properProductOpenMap p q U) (pullback.snd p (U.ι ≫ q))
      (pullback.snd p q) U.ι := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p q) (v₁₃ := p) (h₂₂ := q)
    _ (ProductOpen.Construction.properProductOpenMap_snd p q U) (IsPullback.of_hasPullback p q)
  rw [ProductOpen.Construction.properProductOpenMap_fst]
  exact IsPullback.of_hasPullback p (U.ι ≫ q)

/-- Its image is exactly the preimage of the open in the base. -/
theorem properProductOpen_range :
    Set.range (ProductOpen.Construction.properProductOpenMap p q U) = (pullback.snd p q) ⁻¹' (U : Set Y) := by
  let h := properProductOpen_isPullback p q U
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProperProductOpenGeometry.Construction
