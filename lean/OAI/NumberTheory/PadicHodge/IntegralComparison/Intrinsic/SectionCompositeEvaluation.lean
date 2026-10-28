import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation

/-! # Section Composite Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionCompositeEvaluation

noncomputable section

/-! Evaluating the composite geometric section is the composite of
the original pullback of functions and section evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)

include hs in
theorem over_base : (s ≫ f.left) ≫ Y.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w, hs]

variable (U : Y.left.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ U))

theorem evaluation :
    SectionEvaluation.evaluation R Y (s ≫ f.left) (over_base R X Y f s hs) U hU =
      (SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hU).comp
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U) := by
  apply AlgHom.ext
  intro a
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom ((s ≫ f.left).appLE U ⊤ hU a) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (s.appLE (f.left ⁻¹ᵁ U) ⊤ hU (f.left.app U a))
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem kernel :
    RingHom.ker ((SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hU).toRingHom.comp
      (f.left.app U).hom) =
    RingHom.ker (SectionEvaluation.evaluation R Y (s ≫ f.left)
      (over_base R X Y f s hs) U hU).toRingHom :=
  congrArg (fun e => RingHom.ker e.toRingHom) (evaluation R X Y f s hs U hU).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionCompositeEvaluation
