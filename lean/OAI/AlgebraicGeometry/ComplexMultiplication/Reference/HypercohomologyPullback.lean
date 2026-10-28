import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage

/-! # Hypercohomology Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyPullback

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Actual analytic inverse image on the original hypercohomology

The source is the original constant integer complex in the original derived
category. Exact inverse image induces pullback, natural in actual complex maps.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint
open Localization

variable {X Y : Over (Spec (.of ℂ))}

local instance originalInverseImageLocalizer_commShift (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.CommShift ℤ :=
  inferInstanceAs
    (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ)

/-- Inverse image acts on the original localized morphism definition of hypercohomology. -/
def originalHypercohomologyPullback (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ) :
    ℍ^n(Y; K) → ℍ^n(X; (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) :=
  (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).smallShiftedHomMap
    (AnalyticInverseImage.originalIntegerComplexInverseImageIso f) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Pullback commutes with the original map on hypercohomology of actual complex morphisms. -/
theorem originalHypercohomologyPullback_naturality (f : X ⟶ Y)
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ} (g : K ⟶ L)
    (n : ℤ) (α : ℍ^n(Y; K)) :
    originalHypercohomologyPullback f L n (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y g n α) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map g) n
        (originalHypercohomologyPullback f K n α) := by
  let Φ := AnalyticInverseImage.originalAnalyticInverseImageLocalizer f
  let eI : Φ.functor.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y) ≅
      ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X := AnalyticInverseImage.originalIntegerComplexInverseImageIso f
  change Φ.smallShiftedHomMap eI (Iso.refl (Φ.functor.obj L))
      (α.comp (.mk₀ (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) 0 rfl g) (zero_add n)) =
    (Φ.smallShiftedHomMap eI (Iso.refl (Φ.functor.obj K)) α).comp
      (.mk₀ (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) 0 rfl
        (Φ.functor.map g)) (zero_add n)
  rw [LocalizerMorphism.smallShiftedHomMap_comp Φ eI
    (Iso.refl (Φ.functor.obj K)) (Iso.refl (Φ.functor.obj L)),
    LocalizerMorphism.smallShiftedHomMap_mk₀]
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyPullback
