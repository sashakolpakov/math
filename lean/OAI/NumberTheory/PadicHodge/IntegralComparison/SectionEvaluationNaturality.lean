import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation

/-! # Section Evaluation Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEvaluationNaturality

noncomputable section

/-! Literal evaluation at a section commutes with pullback of regular
functions along a morphism over the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ U)

include hs in
theorem image_retraction : (s ≫ f.left) ≫ Y.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w f]
  exact hs

theorem pullback (a : Γ(Y.left,U)) :
    Intrinsic.SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hU (f.left.app U a) =
      Intrinsic.SectionEvaluation.evaluation R Y (s ≫ f.left)
        (image_retraction R X Y f s hs) U hU a := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (s.appLE (f.left ⁻¹ᵁ U) ⊤ hU (f.left.app U a)) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom ((s ≫ f.left).appLE U ⊤ hU a)
  rw [Scheme.Hom.comp_appLE]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEvaluationNaturality
