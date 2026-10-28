import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComplexComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Clopen
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralFamily

/-! # Integral Component -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The CM point on the original fine PEL space can be chosen in each
literal complex fiber of the supplied integral components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

def Models.RankThreePELModel.integralComplexComponentFinePELMap (a : M.Family) (t : Fin (M.componentCount a)) :
    M.integralComplexComponent a t ⟶ (M.moduli a).complexFiber M.complexEmbedding :=
  M.integralComplexComponentInclusion a t ≫ M.integralComplexFinePELMap a

theorem Models.RankThreePELModel.integralComplexComponentFinePELMap_clopen_range
    (a : M.Family) (t : Fin (M.componentCount a)) :
    IsClopen (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t))) := by
  let e := M.integralComplexFinePELHomeomorph a
  let f := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentInclusion a t)
  have hf : IsClopen (Set.range f) :=
    ⟨(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion _).isClosed_range,
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion _).isOpen_range⟩
  have hr : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t)) =
      e '' Set.range f := by
    rw [← Set.range_comp]
    congr 1
  rw [hr]
  exact ⟨e.isClosedMap _ hf.1, e.isOpenMap _ hf.2⟩

def Models.RankThreePELModel.integralComplexComponentBasePoint (a : M.Family) (t : Fin (M.componentCount a)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t) :=
  Over.homMk (pullback.lift (M.arithmetic.complexPoint ≫ ((M.components a).x₀ t).left)
    (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (by
      rw [Category.assoc, ((M.components a).x₀ t).w]
      change M.arithmetic.complexPoint ≫ 𝟙 M.arithmetic.base = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase ≫ _
      rw [Category.comp_id, Category.id_comp]))
    (pullback.lift_snd _ _ _)

theorem Models.RankThreePELModel.exists_CM_point_on_integral_complex_component
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput) (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t),
      (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x)).HasCMH1 := by
  obtain ⟨hP, hiota, hN, hFine, hball, _⟩ := hM.2.2 a
  exact Clopen.exists_CM_point_in_finePEL_clopen_range hperiod (M.datum a) hP M.iota M.complexEmbedding
    (M.moduli a) hiota hN hFine hball
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t))
    (M.integralComplexComponentFinePELMap_clopen_range a t)
    (M.integralComplexComponentBasePoint a t)

theorem Models.RankThreePELModel.exists_native_CM_point_on_integral_component
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput) (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t),
      (IntrinsicFiber.nativePolarizedAt (M.componentPolarized a t)
        (x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint)).HasCMH1 := by
  obtain ⟨x, hx⟩ := M.exists_CM_point_on_integral_complex_component hperiod hM a t
  let y := x ≫ M.integralComplexComponentInclusion a t
  have hy : (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) y)).HasCMH1 := by
    have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) y =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x :=
      Category.assoc _ _ _
    exact he.symm ▸ hx
  have hCM := (M.nativeIntegralFiber_hasCMH1_iff a y).mpr hy
  have hp : y.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.complexPoint =
      (x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint) ≫
        (M.integralComponentInclusion a t).left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => x.left ≫ k)
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.integralComponentInclusion a t)
          M.arithmetic.complexPoint)).trans (Category.assoc _ _ _).symm)
  refine ⟨x, (IntrinsicFiber.nativePolarizedAt_pullback_hasCMH1_iff
    (M.integral a).universal.data.polarized (M.integralComponentInclusion a t).left _).mpr ?_⟩
  exact hp ▸ hCM

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
