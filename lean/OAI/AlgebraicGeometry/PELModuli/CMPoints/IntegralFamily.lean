import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComplexComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber

/-! # Integral Family -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The supplied IntegralModel universal-family isomorphism identifies the CM
property of the actual integral and original fine-moduli fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

def Models.RankThreePELModel.integralComplexGenericProjection (a : M.Family) :
    (M.integralComplexModuli a).left ⟶
      ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver).left :=
  ((Over.pullbackComp (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))
    M.arithmetic.generic).app (M.integral a).toOver).hom.left ≫
      pullback.fst ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver).hom
        (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))

theorem Models.RankThreePELModel.integralComplexGenericProjection_fst (a : M.Family) :
    M.integralComplexGenericProjection a ≫
      pullback.fst (M.integral a).toOver.hom M.arithmetic.generic =
        pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint := by
  dsimp only [Models.RankThreePELModel.integralComplexGenericProjection]
  exact (Category.assoc _ _ _).trans
    (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst (M.integral a).toOver M.arithmetic.generic
      (Spec.map (CommRingCat.ofHom M.arithmetic.embedding)))

theorem Models.RankThreePELModel.integralComplexReductionIso_fst (a : M.Family) :
    (M.integralComplexReductionIso a).hom.left ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom
        (Spec.map (CommRingCat.ofHom M.complexEmbedding)) =
    M.integralComplexGenericProjection a ≫ (M.integral a).genericIso.hom.left ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension := by
  let c := Spec.map (CommRingCat.ofHom M.arithmetic.embedding)
  let u := ((Over.pullbackComp c M.arithmetic.generic).app (M.integral a).toOver).hom
  let v := (Over.pullback c).map (M.integral a).genericIso.hom
  let w := (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso M.arithmetic
    (IntegralModel.Reduction.reduction (M.moduli a).space)).hom
  have hw := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_fst M.arithmetic
    (IntegralModel.Reduction.reduction (M.moduli a).space)
  have hv := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.integral a).genericIso.hom c
  have hcalc : (u.left ≫ (v.left ≫ w.left)) ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom
        (Spec.map (CommRingCat.ofHom M.complexEmbedding)) =
      (u.left ≫ pullback.fst ((Over.pullback M.arithmetic.generic).obj
        (M.integral a).toOver).hom c) ≫ (M.integral a).genericIso.hom.left ≫
        pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension := by
    simp only [Category.assoc]
    rw [show w.left ≫ _ = _ from hw]
    rw [← Category.assoc v.left]
    exact (congrArg (fun k => u.left ≫ k ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension) hv).trans
        (congrArg (fun k => u.left ≫ k) (Category.assoc _ _ _))
  exact hcalc

theorem Models.RankThreePELModel.integralComplexFinePELMap_fst (a : M.Family) :
    (M.integralComplexFinePELMap a).left ≫
      pullback.fst (M.moduli a).space.hom (Spec.map (CommRingCat.ofHom M.complexEmbedding)) =
    M.integralComplexGenericProjection a ≫ (M.integral a).genericIso.hom.left ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
        (IntegralModel.Reduction.reductionι (M.moduli a).space).left := by
  have hr := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (IntegralModel.Reduction.reductionι (M.moduli a).space)
    (Spec.map (CommRingCat.ofHom M.complexEmbedding))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (M.integralComplexReductionIso a).hom.left ≫ k) hr).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (IntegralModel.Reduction.reductionι (M.moduli a).space).left)
          (M.integralComplexReductionIso_fst a)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => M.integralComplexGenericProjection a ≫ k)
              (Category.assoc _ _ _))))))

theorem Models.RankThreePELModel.nativeIntegralFiber_hasCMH1_iff (a : M.Family)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexModuli a)) :
    (IntrinsicFiber.nativePolarizedAt (M.integral a).universal.data.polarized
      (x.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint)).HasCMH1 ↔
    (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) x)).HasCMH1 := by
  let p := x.left ≫ M.integralComplexGenericProjection a
  let e := (M.integral a).familyIso.abelian
  have h := IntrinsicFiber.nativePolarizedAt_iso_hasCMH1_iff
    (P := (M.integral a).universal.data.polarized.pullback
      (pullback.fst (M.integral a).toOver.hom M.arithmetic.generic))
    (Q := (M.moduli a).universal.polarized.pullback
      ((M.integral a).genericIso.hom.left ≫
        pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
          (IntegralModel.Reduction.reductionι (M.moduli a).space).left)) e p
  rw [IntrinsicFiber.nativePolarizedAt_pullback_hasCMH1_iff,
    IntrinsicFiber.nativePolarizedAt_pullback_hasCMH1_iff] at h
  have hl : p ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.generic =
      x.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint := by
    dsimp only [p]
    rw [Category.assoc, Models.RankThreePELModel.integralComplexGenericProjection_fst]
  have hr : p ≫ ((M.integral a).genericIso.hom.left ≫
      pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
        (IntegralModel.Reduction.reductionι (M.moduli a).space).left) =
      IntrinsicFiber.finePELComplexPoint (M.moduli a) M.complexEmbedding
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) x) := by
    change (x.left ≫ M.integralComplexGenericProjection a) ≫ _ =
      (x.left ≫ (M.integralComplexFinePELMap a).left) ≫ _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => x.left ≫ k) (M.integralComplexFinePELMap_fst a).symm).trans
        (Category.assoc _ _ _).symm)
  change (IntrinsicFiber.nativePolarizedAt _ _).HasCMH1 ↔ (IntrinsicFiber.nativePolarizedAt _ _).HasCMH1
  simpa only [hl, hr, IntegralModel.PEL.Has.characteristicZeroPELData] using h

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
