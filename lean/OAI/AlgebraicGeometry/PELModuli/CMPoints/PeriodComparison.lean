import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Period Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodComparison

noncomputable section

/-! The additional general universal-family comparison prerequisite.
It compares every period of a covering chart with the actual universal
abelian fiber. It assumes no CM point, ordinary fiber, or density. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

structure UniversalPELPeriodChart
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) {iota : E →+* K} (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (κ : K →+* ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ M.complexFiber κ) where
  matrix : Matrix (Fin 3) (Fin 3) E
  hermitian : ∀ i j, matrix i j = NumberField.IsCMField.complexConj E (matrix j i)
  anisotropic : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian matrix x x = 0 → x = 0
  normalizer : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec
  normalizes : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ matrix (normalizer x) (normalizer y) =
    AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y
  cover : P.Domain → X.analyticSpace
  isCover : P.IsBallCover X cover
  hodge : P.Domain → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E)
  realization : ∀ z, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (hodge z)
  fiber : ∀ z, (realization z).abelianVariety =
    IntrinsicFiber.nativeFinePELAt M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (cover z))
  periods : ∀ z x, x ∈ (hodge z).holomorphic ↔
    ClosedCoefficientPeriods.componentPrescribed P matrix (normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (PeriodCoordinates.cmPeriodCoordinates P hP x)

/-- General comparison for every actual projective component of a fine
PEL moduli space. The covering parameter is tied to the original
universal family's literal fibers at every point of the ball. -/
def UniversalPELPeriodComparisonInput : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (s N : ℕ) (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N),
    κ.comp iota = P.μ → IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N → M.IsFine →
    ∀ (C : M.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (f : X.toOver ⟶ M.complexFiber κ),
      X.complexDimension = 2 → IsOpenImmersion f.left → IsClosedImmersion f.left →
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) =
        {x : M.ComplexPoints κ | ConnectedComponents.mk x = C} →
      Nonempty (UniversalPELPeriodChart P hP M κ X f)

theorem UniversalPELPeriodChart.exists_CM_point
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {hP : P.IsAdmissible} {iota : E →+* K} {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N}
    {κ : K →+* ℂ} {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {f : X.toOver ⟶ M.complexFiber κ}
    (T : UniversalPELPeriodChart P hP M κ X f) :
    ∃ x : X.analyticSpace, (IntrinsicFiber.nativeFinePELAt M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)).HasCMH1 := by
  obtain ⟨z, hz⟩ := PeriodRealization.exists_CM_fiber_of_universal_period_comparison P hP T.matrix
    T.hermitian T.anisotropic T.normalizer T.normalizes T.hodge T.realization T.periods
  exact ⟨T.cover z, (T.fiber z) ▸ hz⟩

/-- Every actual analytic component contains a CM fiber. CM existence is
derived from the universal comparison, rational negative lines and RiemannProjectivity. -/
theorem exists_CM_point_on_finePEL_component
    (hperiod : UniversalPELPeriodComparisonInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hiota : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine)
    (hball : M.HasProjectiveBallComponents κ) (C : M.ComplexComponent κ) :
    ∃ x : M.ComplexPoints κ,
      ConnectedComponents.mk x = C ∧ (IntrinsicFiber.nativeFinePELAt M κ x).HasCMH1 := by
  obtain ⟨X, ⟨hdim, f, hopen, hclosed, hrange⟩, _⟩ := hball C
  obtain ⟨T⟩ := hperiod E K s N P hP iota κ M hiota hN hM
    C X f hdim hopen hclosed hrange
  obtain ⟨x, hx⟩ := T.exists_CM_point
  refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x, ?_, hx⟩
  have hm : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
    ⟨x, rfl⟩
  rw [hrange] at hm
  exact hm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodComparison
