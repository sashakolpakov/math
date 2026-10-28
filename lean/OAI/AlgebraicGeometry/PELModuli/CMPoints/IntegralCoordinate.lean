import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateFibers
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFieldPoint

/-! # Integral Coordinate -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Retain the three specified CM types in the literal polarized fiber
over the descended point on each original integral component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.nativeIntegralFiber_coordinateCM_iff (hM : M.HasPrescribedBallPeriods) (a : M.Family)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexModuli a)) :
    CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
      (IntrinsicFiber.nativePolarizedAt (M.integral a).universal.data.polarized
        (x.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint)) ↔
    CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
      (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) x)) := by
  let p := x.left ≫ M.integralComplexGenericProjection a
  let e := (M.integral a).familyIso.abelian
  have h := CoordinateFibers.nativePolarizedAt_iso_coordinateCM_iff
    (P := M.datum a) (hP := (hM.2.2 a).1)
    (Q := (M.integral a).universal.data.polarized.pullback
      (pullback.fst (M.integral a).toOver.hom M.arithmetic.generic))
    (T := (M.moduli a).universal.polarized.pullback
      ((M.integral a).genericIso.hom.left ≫
        pullback.fst (IntegralModel.Reduction.reduction (M.moduli a).space).hom M.arithmetic.fieldExtension ≫
          (IntegralModel.Reduction.reductionι (M.moduli a).space).left)) e p
  rw [CoordinateFibers.nativePolarizedAt_pullback_coordinateCM_iff,
    CoordinateFibers.nativePolarizedAt_pullback_coordinateCM_iff] at h
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
  simpa only [hl, hr, IntegralModel.PEL.Has.characteristicZeroPELData, IntrinsicFiber.nativeFinePELAt] using h

theorem Models.RankThreePELModel.nativeComponentFiber_coordinateCM_iff (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
      (IntrinsicFiber.nativePolarizedAt (M.componentPolarized a t)
        (x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint)) ↔
    CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
      (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x)) := by
  let y := x ≫ M.integralComplexComponentInclusion a t
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) y =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x := Category.assoc _ _ _
  have hCM := M.nativeIntegralFiber_coordinateCM_iff hM a y
  rw [he] at hCM
  have hp : y.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint =
      (x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint) ≫
        (M.integralComponentInclusion a t).left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => x.left ≫ k)
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.integralComponentInclusion a t)
          M.arithmetic.complexPoint)).trans (Category.assoc _ _ _).symm)
  exact (CoordinateFibers.nativePolarizedAt_pullback_coordinateCM_iff
    (M.integral a).universal.data.polarized (M.integralComponentInclusion a t).left _).trans
      (hp ▸ hCM)

theorem Models.RankThreePELModel.exists_coordinate_CM_native_arithmetic_component_point
    [IsGalois ℚ E]
    (hCMAbelianVariety : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ F : Subfield ℂ, NumberField F ∧
      ∃ (i : M.arithmetic.extension.carrier →+* F)
        (p : Spec (.of F) ⟶ ((M.components a).S t).left),
        F.subtype.comp i = M.arithmetic.embedding ∧
        p ≫ ((M.components a).S t).hom = Spec.map (CommRingCat.ofHom i) ≫ M.arithmetic.generic ∧
        CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
          (IntrinsicFiber.nativePolarizedAt (M.componentPolarized a t)
            (Spec.map (CommRingCat.ofHom F.subtype) ≫ p)) := by
  obtain ⟨x, F, hF, i, p, hi, hb, hc, hCM⟩ :=
    M.exists_coordinate_CM_arithmetic_component_point a t hCMAbelianVariety hM
  refine ⟨F, hF, i, p, hi, hb, ?_⟩
  rw [hc]
  exact (M.nativeComponentFiber_coordinateCM_iff hM a t x).mpr hCM

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
