import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodComparison
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Clopen -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Clopen

noncomputable section

/-! The constructed CM point can be retained in any nonempty actual
open-and-closed piece of the complex PEL scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_CM_point_in_finePEL_clopen_range
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hiota : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine)
    (hball : M.HasProjectiveBallComponents κ)
    {X : Type*} (f : X → M.ComplexPoints κ) (hclopen : IsClopen (Set.range f))
    (x₀ : X) :
    ∃ x : X, (IntrinsicFiber.nativeFinePELAt M κ (f x)).HasCMH1 := by
  obtain ⟨y, hy, hCM⟩ := PeriodComparison.exists_CM_point_on_finePEL_component hperiod P hP iota κ M
    hiota hN hM hball (ConnectedComponents.mk (f x₀))
  have hyc : y ∈ connectedComponent (f x₀) :=
    ConnectedComponents.coe_eq_coe'.mp hy
  obtain ⟨x, hx⟩ := hclopen.connectedComponent_subset ⟨x₀, rfl⟩ hyc
  exact ⟨x, hx ▸ hCM⟩

theorem exists_CM_point_on_finePEL_clopen
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hiota : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine)
    (hball : M.HasProjectiveBallComponents κ)
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (f : X ⟶ M.complexFiber κ)
    [IsOpenImmersion f.left] [IsClosedImmersion f.left]
    (x₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      (IntrinsicFiber.nativeFinePELAt M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)).HasCMH1 :=
  exists_CM_point_in_finePEL_clopen_range hperiod P hP iota κ M hiota hN hM hball
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
    ⟨(AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).isClosed_range,
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f).isOpen_range⟩ x₀

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Clopen
