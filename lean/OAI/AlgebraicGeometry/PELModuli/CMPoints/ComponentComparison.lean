import OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericModuliCM
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddedComplexComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComponent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexGenericNaturality

/-! # Component Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Compatibility of the arithmetic moduli point with its original
fine-moduli point, retaining the chosen open-and-closed component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.genericModuliFinePoint_component (a : M.Family) (t : Fin (M.componentCount a))
    (z : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.embeddedGenericComponent a t).left) :
    M.genericModuliFinePoint a (z ≫ (M.embeddedGenericComponentInclusion a t).left) =
    (((z ≫ pullback.fst (M.genericComponent a t).hom
      (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))) ≫
        (M.genericComponentInclusion a t).left) ≫
          pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension) ≫
            (IntegralModel.Reduction.reductionι (M.moduli a).space).left := by
  let p := z ≫ (M.embeddedGenericComponentInclusion a t).left
  let c := Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField)
  have h₁ : (p ≫ (M.embeddedGenericInclusion a).left) ≫
      pullback.fst (M.genericFinePEL a).space.hom c =
      (p ≫ pullback.fst (M.reducedGenericModuli a).hom c) ≫
        (M.reducedGenericInclusion a).left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => p ≫ k)
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.reducedGenericInclusion a) c)).trans
          (Category.assoc _ _ _).symm)
  have h₂ : p ≫ pullback.fst (M.reducedGenericModuli a).hom c =
      (z ≫ pullback.fst (M.genericComponent a t).hom c) ≫
        (M.genericComponentInclusion a t).left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => z ≫ k)
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.genericComponentInclusion a t) c)).trans
          (Category.assoc _ _ _).symm)
  have h₃ := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (IntegralModel.Reduction.reductionι (M.moduli a).space)
    M.arithmetic.fieldExtension
  exact (congrArg (fun k => k ≫
    pullback.fst (M.moduli a).space.hom M.arithmetic.fieldExtension) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (p ≫ pullback.fst (M.reducedGenericModuli a).hom c) ≫ k) h₃).trans
          ((congrArg (fun k => k ≫
            (pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
              (IntegralModel.Reduction.reductionι (M.moduli a).space).left)) h₂).trans
                (Category.assoc _ _ _).symm)))

theorem Models.RankThreePELModel.embeddedComponentPoint_finePoint (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    M.genericModuliFinePoint a
      (M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponentInclusion a t).left) =
    IntrinsicFiber.finePELComplexPoint (M.moduli a) M.complexEmbedding
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x) := by
  let f := M.integralComponentInclusion a t
  let y := x ≫ M.integralComplexComponentInclusion a t
  let p := (x.left ≫ ComplexGenericNaturality.arithmeticComplexGenericProjection M.arithmetic ((M.components a).S t)) ≫
    ((Over.pullback M.arithmetic.generic).map f).left
  let r := (M.integral a).genericIso.hom.left ≫
    pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
      (IntegralModel.Reduction.reductionι (M.moduli a).space).left
  have hp : y.left ≫ M.integralComplexGenericProjection a = p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => x.left ≫ k)
        (ComplexGenericNaturality.arithmeticComplexGenericProjection_naturality M.arithmetic f)).trans
          (Category.assoc _ _ _).symm)
  have hg := M.embeddedComponentPoint_generic a t x
  have hleft : M.genericModuliFinePoint a
      (M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponentInclusion a t).left) = p ≫ r := by
    rw [Models.RankThreePELModel.genericModuliFinePoint_component]
    have hh := congrArg (fun k => ((k ≫ (M.genericComponentInclusion a t).left) ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension) ≫
        (IntegralModel.Reduction.reductionι (M.moduli a).space).left) hg
    refine hh.trans ?_
    change ((((x.left ≫ _) ≫ _) ≫ (_ ≫ _)) ≫ _) ≫ _ = _
    simp only [p, r, ComplexGenericNaturality.arithmeticComplexGenericProjection, Category.assoc]
    exact congrArg (fun k => x.left ≫ k) (Category.assoc _ _ _).symm
  have hright : IntrinsicFiber.finePELComplexPoint (M.moduli a) M.complexEmbedding
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) y) = p ≫ r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => y.left ≫ k) (M.integralComplexFinePELMap_fst a)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ r) hp)))
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) y =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x :=
    Category.assoc _ _ _
  exact hleft.trans (hright.symm.trans (congrArg
    (IntrinsicFiber.finePELComplexPoint (M.moduli a) M.complexEmbedding) he))

theorem Models.RankThreePELModel.embeddedComponentPoint_hasCMH1_iff (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    ((M.genericStandardModuli hM a).abelianAt
      (M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponentInclusion a t).left)).HasCMH1 ↔
    (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x)).HasCMH1 := by
  have h := M.genericStandardModuli_hasCMH1_iff hM a
    (M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponentInclusion a t).left)
  exact h.trans (iff_of_eq (congrArg (fun p =>
    (IntrinsicFiber.nativePolarizedAt (M.moduli a).universal.polarized p).HasCMH1)
      (M.embeddedComponentPoint_finePoint a t x)))

theorem Models.RankThreePELModel.exists_CM_point_over_numberField_on_component
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput) (hCMAbelianVariety : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) (F : Subfield ℂ),
      NumberField F ∧
      ((M.genericStandardModuli hM a).abelianAt
        (M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponentInclusion a t).left)).HasCMH1 ∧
      ∃ p : Spec (.of F) ⟶ (M.embeddedGenericComponent a t).left,
        Spec.map (CommRingCat.ofHom F.subtype) ≫ p = M.embeddedComponentPoint a t x := by
  obtain ⟨x, hx⟩ := M.exists_CM_point_on_integral_complex_component hperiod hM a t
  have hCM := (M.embeddedComponentPoint_hasCMH1_iff hM a t x).mpr hx
  obtain ⟨F, hF, p, hp⟩ := M.component_CM_point_descends hCMAbelianVariety hM a t
    (M.embeddedComponentPoint a t x) hCM
  exact ⟨x, F, hF, hCM, p, hp⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
