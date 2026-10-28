import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ConormalRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ActionCharts

/-! # Conormal Action -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section

noncomputable section

/-! Actual section-preserving maps induce endomorphisms of one
finite projective conormal module on each constructed affine base chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} {p : Y ⟶ X} [Smooth p] {s : X ⟶ Y}
  {ι : Type} {f : ι → (Y ⟶ Y)} (C : ActionCharts.SectionMorphismChart p s f)
  (hs : s ≫ p = 𝟙 X) (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s)

def ActionCharts.SectionMorphismChart.conormalRestriction :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    (RingHom.ker C.targetSection.appTop.hom).Cotangent ≃ₗ[Γ(C.V.toScheme, ⊤)]
      (RingHom.ker C.sourceSection.appTop.hom).Cotangent :=
  Affine.ConormalRestriction.AffineSectionConormal.restrictionEquiv C.sourceProjection C.targetProjection
    C.sourceSection C.targetSection (C.source_retraction hs) (C.target_retraction hs)
    C.inclusionMap C.inclusion_over C.inclusion_section

def ActionCharts.SectionMorphismChart.conormalOperator (i : ι) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    Module.End Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  exact (C.conormalRestriction hs).symm.toLinearMap.comp
    (Affine.ConormalRestriction.AffineSectionConormal.map C.sourceProjection C.targetProjection
      C.sourceSection C.targetSection (C.source_retraction hs) (C.target_retraction hs)
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i))

theorem ActionCharts.SectionMorphismChart.conormalOperator_restriction (i : ι) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    (C.conormalRestriction hs).toLinearMap.comp (C.conormalOperator hs hf he i) =
      Affine.ConormalRestriction.AffineSectionConormal.map C.sourceProjection C.targetProjection
        C.sourceSection C.targetSection (C.source_retraction hs) (C.target_retraction hs)
        (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  apply LinearMap.ext
  intro v
  exact (C.conormalRestriction hs).apply_symm_apply _

include hs in
theorem ActionCharts.SectionMorphismChart.conormal_finite_projective :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    Module.Finite Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent ∧
      Module.Projective Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent :=
  Affine.ConormalRestriction.AffineSectionConormal.finite_projective C.targetProjection C.targetSection (C.target_retraction hs)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section
