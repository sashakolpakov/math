import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.AffineLieNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentOpenRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalAction

/-! # Tangent Action -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section

noncomputable section

/-! The actual tangent action on a simultaneous affine chart is
dual to its constructed conormal action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y}
  {I : Type} {f : I → (Y ⟶ Y)} (C : ActionCharts.SectionMorphismChart p s f)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ C.V.toScheme)

def ActionCharts.SectionMorphismChart.tangentRestriction :
    Affine.SectionLie.AffineSectionLie.Space C.sourceProjection C.sourceSection q ≃ₗ[k]
      Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q := by
  let m := AffineLieNaturality.AffineSectionLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
    C.inclusionMap C.inclusion_over C.inclusion_section
  have hm : Function.Bijective m := Relative.TangentOpenRestriction.RelativeTangent.map_bijective_of_open
    (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    C.sourceProjection (Affine.SectionLie.AffineSectionLie.zeroPoint C.sourceSection q)
    C.targetProjection (Affine.SectionLie.AffineSectionLie.zeroPoint C.targetSection q) C.inclusionMap (𝟙 C.V.toScheme)
    (C.inclusion_over.trans (Category.comp_id C.sourceProjection).symm)
    (AffineLieNaturality.AffineSectionLie.zeroPoint_comp C.sourceSection C.targetSection q C.inclusionMap C.inclusion_section)
  exact LinearEquiv.ofBijective m hm

def ActionCharts.SectionMorphismChart.tangentOperator (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I) :
    Module.End k (Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q) :=
  (AffineLieNaturality.AffineSectionLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
    (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)).comp
      (C.tangentRestriction q).symm.toLinearMap

theorem ActionCharts.SectionMorphismChart.tangentOperator_conormal [Smooth p] (hs : s ≫ p = 𝟙 X)
    (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I)
    (v : Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
    Affine.SectionLie.AffineSectionLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q
        (C.tangentOperator q hf he i v) =
      (Affine.SectionLie.AffineSectionLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q v).comp
        (C.conormalOperator hs hf he i) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
  obtain ⟨w, rfl⟩ := (C.tangentRestriction q).surjective v
  change Affine.SectionLie.AffineSectionLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q
    (AffineLieNaturality.AffineSectionLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
      ((C.tangentRestriction q).symm ((C.tangentRestriction q) w))) = _
  rw [(C.tangentRestriction q).symm_apply_apply]
  have hF := AffineLieNaturality.AffineSectionLie.conormalEquiv_natural C.sourceProjection C.targetProjection
    C.sourceSection C.targetSection q (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
    (C.source_retraction hs) (C.target_retraction hs) w
  have hJ := AffineLieNaturality.AffineSectionLie.conormalEquiv_natural C.sourceProjection C.targetProjection
    C.sourceSection C.targetSection q C.inclusionMap C.inclusion_over C.inclusion_section
    (C.source_retraction hs) (C.target_retraction hs) w
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hF b).trans
    ((congrArg (Affine.SectionLie.AffineSectionLie.conormalEquiv C.sourceProjection C.sourceSection (C.source_retraction hs) q w)
      (LinearMap.congr_fun (C.conormalOperator_restriction hs hf he i) b).symm).trans
        (LinearMap.congr_fun hJ (C.conormalOperator hs hf he i b)).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section
