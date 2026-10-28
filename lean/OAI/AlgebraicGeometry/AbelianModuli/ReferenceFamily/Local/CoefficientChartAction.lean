import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentOpenRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalAction

/-! # Coefficient Chart Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartAction.LocalCoefficientChart

noncomputable section

section

/-! The actual tangent action on a simultaneous affine chart is
dual to its constructed conormal action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y}
  {I : Type} {f : I → (Y ⟶ Y)} (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart p s f)
  {k : Type} [CommRing k] [IsLocalRing k] (q : Spec (.of k) ⟶ C.V.toScheme)

def tangentRestriction :
    CoefficientLieSpace.LocalCoefficientLie.Space C.sourceProjection C.sourceSection q ≃ₗ[k]
      CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q := by
  let m := CoefficientLieNaturality.LocalCoefficientLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
    C.inclusionMap C.inclusion_over C.inclusion_section
  have hm : Function.Bijective m := PELModuli.IntegralModel.Relative.TangentOpenRestriction.RelativeTangent.map_bijective_of_open
    (C := .of (DualNumber k)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal k) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square k)
    C.sourceProjection (CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.sourceSection q)
    C.targetProjection (CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.targetSection q) C.inclusionMap (𝟙 C.V.toScheme)
    (C.inclusion_over.trans (Category.comp_id C.sourceProjection).symm)
    (CoefficientLieNaturality.LocalCoefficientLie.zeroPoint_comp C.sourceSection C.targetSection q C.inclusionMap C.inclusion_section)
  exact LinearEquiv.ofBijective m hm

def tangentOperator (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I) :
    Module.End k (CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q) :=
  (CoefficientLieNaturality.LocalCoefficientLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
    (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)).comp
      (tangentRestriction C q).symm.toLinearMap

theorem tangentOperator_conormal [Smooth p] (hs : s ≫ p = 𝟙 X)
    (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I)
    (v : CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q
        (tangentOperator C q hf he i v) =
      (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q v).comp
        (C.conormalOperator hs hf he i) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.sourceProjection
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  obtain ⟨w, rfl⟩ := (tangentRestriction C q).surjective v
  change CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection (C.target_retraction hs) q
    (CoefficientLieNaturality.LocalCoefficientLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
      ((tangentRestriction C q).symm ((tangentRestriction C q) w))) = _
  rw [(tangentRestriction C q).symm_apply_apply]
  have hF := CoefficientLieNaturality.LocalCoefficientLie.conormalEquiv_natural C.sourceProjection C.targetProjection
    C.sourceSection C.targetSection q (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
    (C.source_retraction hs) (C.target_retraction hs) w
  have hJ := CoefficientLieNaturality.LocalCoefficientLie.conormalEquiv_natural C.sourceProjection C.targetProjection
    C.sourceSection C.targetSection q C.inclusionMap C.inclusion_over C.inclusion_section
    (C.source_retraction hs) (C.target_retraction hs) w
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hF b).trans
    ((congrArg (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.sourceProjection C.sourceSection (C.source_retraction hs) q w)
      (LinearMap.congr_fun (C.conormalOperator_restriction hs hf he i) b).symm).trans
        (LinearMap.congr_fun hJ (C.conormalOperator hs hf he i b)).symm)

end

/-! The chart's actual tangent action agrees with the relative
differential on the original family, under the open-neighborhood comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y}
  {I : Type} {f : I → (Y ⟶ Y)} (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart p s f)
  {k : Type} [CommRing k] [IsLocalRing k] (q : Spec (.of k) ⟶ C.V.toScheme)

omit [IsLocalRing k] in
theorem targetZeroPoint_ι :
    CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.targetSection q ≫ C.U.ι =
      CoefficientLieSpace.LocalCoefficientLie.zeroPoint s (q ≫ C.V.ι) := by
  have hs : C.targetSection ≫ C.U.ι = C.V.ι ≫ s := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι s C.U C.V C.sectionU
  simp only [CoefficientLieSpace.LocalCoefficientLie.zeroPoint, Category.assoc, hs]

def targetTangentEquiv :
    CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q ≃ₗ[k]
      CoefficientLieSpace.LocalCoefficientLie.Space p s (q ≫ C.V.ι) := by
  let hf : C.U.ι ≫ p = C.targetProjection ≫ C.V.ι :=
    (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι p C.U C.V C.overU).symm
  let m : CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q →ₗ[DualNumber k]
      CoefficientLieSpace.LocalCoefficientLie.Space p s (q ≫ C.V.ι) :=
    PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.map (C := .of (DualNumber k)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal k) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square k)
      C.targetProjection (CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.targetSection q)
      p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι hf (targetZeroPoint_ι C q)
  have hm : Function.Bijective m := PELModuli.IntegralModel.Relative.TangentOpenRestriction.RelativeTangent.map_bijective_of_open
    (C := .of (DualNumber k)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal k) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square k)
    C.targetProjection (CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.targetSection q)
    p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι hf (targetZeroPoint_ι C q)
  exact (LinearEquiv.ofBijective m hm).restrictScalars k

theorem targetTangentEquiv_point (v : CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q) :
    CoefficientLieNaturality.LocalCoefficientLie.point p s (q ≫ C.V.ι) (targetTangentEquiv C q v) =
      CoefficientLieNaturality.LocalCoefficientLie.point C.targetProjection C.targetSection q v ≫ C.U.ι :=
  PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point_map (C := .of (DualNumber k)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal k) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square k)
    C.targetProjection (CoefficientLieSpace.LocalCoefficientLie.zeroPoint C.targetSection q)
    p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι
    (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι p C.U C.V C.overU).symm (targetZeroPoint_ι C q) v

theorem tangentRestriction_point (v : CoefficientLieSpace.LocalCoefficientLie.Space C.sourceProjection C.sourceSection q) :
    CoefficientLieNaturality.LocalCoefficientLie.point C.targetProjection C.targetSection q (tangentRestriction C q v) =
      CoefficientLieNaturality.LocalCoefficientLie.point C.sourceProjection C.sourceSection q v ≫ C.inclusionMap :=
  CoefficientLieNaturality.LocalCoefficientLie.point_map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
    C.inclusionMap C.inclusion_over C.inclusion_section v

theorem targetTangentEquiv_operator (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I)
    (v : CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q) :
    targetTangentEquiv C q (tangentOperator C q hf he i v) =
      CoefficientLieNaturality.LocalCoefficientLie.map p p s s (q ≫ C.V.ι) (f i) (hf i) (he i) (targetTangentEquiv C q v) := by
  obtain ⟨w, rfl⟩ := (tangentRestriction C q).surjective v
  change targetTangentEquiv C q
    (CoefficientLieNaturality.LocalCoefficientLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
      ((tangentRestriction C q).symm ((tangentRestriction C q) w))) = _
  rw [(tangentRestriction C q).symm_apply_apply]
  apply CoefficientLieNaturality.LocalCoefficientLie.point_injective p s (q ≫ C.V.ι)
  have hL := (targetTangentEquiv_point C q
    (CoefficientLieNaturality.LocalCoefficientLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i) w)).trans
        (congrArg (fun z => z ≫ C.U.ι)
          (CoefficientLieNaturality.LocalCoefficientLie.point_map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
            (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i) w))
  have hR := (CoefficientLieNaturality.LocalCoefficientLie.point_map p p s s (q ≫ C.V.ι) (f i) (hf i) (he i)
    (targetTangentEquiv C q (tangentRestriction C q w))).trans
      ((congrArg (fun z => z ≫ f i) (targetTangentEquiv_point C q (tangentRestriction C q w))).trans
        (congrArg (fun z => (z ≫ C.U.ι) ≫ f i) (tangentRestriction_point C q w)))
  have hi : C.inclusionMap ≫ C.U.ι = C.W.ι := Scheme.homOfLE_ι Y C.inclusion
  have hmid : (CoefficientLieNaturality.LocalCoefficientLie.point C.sourceProjection C.sourceSection q w ≫ C.actionMap i) ≫ C.U.ι =
      ((CoefficientLieNaturality.LocalCoefficientLie.point C.sourceProjection C.sourceSection q w ≫ C.inclusionMap) ≫ C.U.ι) ≫ f i := by
    rw [Category.assoc, C.actionMap_ι,
      Category.assoc (CoefficientLieNaturality.LocalCoefficientLie.point C.sourceProjection C.sourceSection q w) C.inclusionMap C.U.ι,
      hi, Category.assoc]
  exact hL.trans (hmid.trans hR.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartAction.LocalCoefficientChart
