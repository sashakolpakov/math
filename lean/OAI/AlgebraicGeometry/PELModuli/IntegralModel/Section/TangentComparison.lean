import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.TangentAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.AffineLieNaturality

/-! # Tangent Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section

noncomputable section

/-! The chart's actual tangent action agrees with the relative
differential on the original family, under the open-neighborhood comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y}
  {I : Type} {f : I → (Y ⟶ Y)} (C : ActionCharts.SectionMorphismChart p s f)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ C.V.toScheme)

theorem ActionCharts.SectionMorphismChart.targetZeroPoint_ι :
    Affine.SectionLie.AffineSectionLie.zeroPoint C.targetSection q ≫ C.U.ι =
      Affine.SectionLie.AffineSectionLie.zeroPoint s (q ≫ C.V.ι) := by
  have hs : C.targetSection ≫ C.U.ι = C.V.ι ≫ s := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι s C.U C.V C.sectionU
  dsimp only [Affine.SectionLie.AffineSectionLie.zeroPoint]
  rw [Category.assoc, Category.assoc, hs, Category.assoc]

def ActionCharts.SectionMorphismChart.targetTangentEquiv :
    Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q ≃ₗ[k]
      Affine.SectionLie.AffineSectionLie.Space p s (q ≫ C.V.ι) := by
  let hf : C.U.ι ≫ p = C.targetProjection ≫ C.V.ι :=
    (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι p C.U C.V C.overU).symm
  let m : Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q →ₗ[DualNumber k]
      Affine.SectionLie.AffineSectionLie.Space p s (q ≫ C.V.ι) :=
    Relative.TangentBaseChange.RelativeTangent.map (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
      C.targetProjection (Affine.SectionLie.AffineSectionLie.zeroPoint C.targetSection q)
      p (Affine.SectionLie.AffineSectionLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι hf (C.targetZeroPoint_ι q)
  have hm : Function.Bijective m := Relative.TangentOpenRestriction.RelativeTangent.map_bijective_of_open
    (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    C.targetProjection (Affine.SectionLie.AffineSectionLie.zeroPoint C.targetSection q)
    p (Affine.SectionLie.AffineSectionLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι hf (C.targetZeroPoint_ι q)
  exact (LinearEquiv.ofBijective m hm).restrictScalars k

theorem ActionCharts.SectionMorphismChart.targetTangentEquiv_point (v : Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q) :
    AffineLieNaturality.AffineSectionLie.point p s (q ≫ C.V.ι) (C.targetTangentEquiv q v) =
      AffineLieNaturality.AffineSectionLie.point C.targetProjection C.targetSection q v ≫ C.U.ι :=
  Relative.TangentBaseChange.RelativeTangent.point_map (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    C.targetProjection (Affine.SectionLie.AffineSectionLie.zeroPoint C.targetSection q)
    p (Affine.SectionLie.AffineSectionLie.zeroPoint s (q ≫ C.V.ι)) C.U.ι C.V.ι
    (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι p C.U C.V C.overU).symm (C.targetZeroPoint_ι q) v

theorem ActionCharts.SectionMorphismChart.tangentRestriction_point (v : Affine.SectionLie.AffineSectionLie.Space C.sourceProjection C.sourceSection q) :
    AffineLieNaturality.AffineSectionLie.point C.targetProjection C.targetSection q (C.tangentRestriction q v) =
      AffineLieNaturality.AffineSectionLie.point C.sourceProjection C.sourceSection q v ≫ C.inclusionMap :=
  AffineLieNaturality.AffineSectionLie.point_map C.sourceProjection C.sourceSection q C.targetProjection C.targetSection
    C.inclusionMap C.inclusion_over C.inclusion_section v

theorem ActionCharts.SectionMorphismChart.targetTangentEquiv_operator (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (i : I)
    (v : Affine.SectionLie.AffineSectionLie.Space C.targetProjection C.targetSection q) :
    C.targetTangentEquiv q (C.tangentOperator q hf he i v) =
      AffineLieNaturality.AffineSectionLie.map p p s s (q ≫ C.V.ι) (f i) (hf i) (he i) (C.targetTangentEquiv q v) := by
  obtain ⟨w, rfl⟩ := (C.tangentRestriction q).surjective v
  change C.targetTangentEquiv q
    (AffineLieNaturality.AffineSectionLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i)
      ((C.tangentRestriction q).symm ((C.tangentRestriction q) w))) = _
  rw [(C.tangentRestriction q).symm_apply_apply]
  apply AffineLieNaturality.AffineSectionLie.point_injective p s (q ≫ C.V.ι)
  have hL := (C.targetTangentEquiv_point q
    (AffineLieNaturality.AffineSectionLie.map C.sourceProjection C.targetProjection C.sourceSection C.targetSection q
      (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i) w)).trans
        (congrArg (fun z => z ≫ C.U.ι)
          (AffineLieNaturality.AffineSectionLie.point_map C.sourceProjection C.sourceSection q C.targetProjection C.targetSection
            (C.actionMap i) (C.actionMap_over hf i) (C.actionMap_section he i) w))
  have hR := (AffineLieNaturality.AffineSectionLie.point_map p s (q ≫ C.V.ι) p s (f i) (hf i) (he i)
    (C.targetTangentEquiv q (C.tangentRestriction q w))).trans
      ((congrArg (fun z => z ≫ f i) (C.targetTangentEquiv_point q (C.tangentRestriction q w))).trans
        (congrArg (fun z => (z ≫ C.U.ι) ≫ f i) (C.tangentRestriction_point q w)))
  have hi : C.inclusionMap ≫ C.U.ι = C.W.ι := Scheme.homOfLE_ι Y C.inclusion
  have hmid : (AffineLieNaturality.AffineSectionLie.point C.sourceProjection C.sourceSection q w ≫ C.actionMap i) ≫ C.U.ι =
      ((AffineLieNaturality.AffineSectionLie.point C.sourceProjection C.sourceSection q w ≫ C.inclusionMap) ≫ C.U.ι) ≫ f i := by
    rw [Category.assoc, C.actionMap_ι,
      Category.assoc (AffineLieNaturality.AffineSectionLie.point C.sourceProjection C.sourceSection q w) C.inclusionMap C.U.ι,
      hi, Category.assoc]
  exact hL.trans (hmid.trans hR.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section
