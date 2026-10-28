import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedChartPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodCoordinateContinuity

/-! # Continuous Presented Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian

noncomputable section

/-!
Continuous full chart-period bases yield continuous genuine marked period
matrices after an actual geometric presentation. The choices of geometric
presentation and of complex tangent equivalence need no continuity premise:
the exact coordinate comparisons prove the required continuity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

abbrev abelianSchemeNativeModel {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral A.scheme.left] :=
  Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {S V : Type} [TopologicalSpace S]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
  {g : ℕ} (A : S → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  [∀ s, IsIntegral (A s).scheme.left] [∀ s, T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme)]

local instance (s : S) : LieGroup (𝓘(ℝ, abelianSchemeNativeModel (A s))) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) :=
  IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (A s).scheme

theorem exists_continuous_presented_periods
    (P : ∀ s, StandardModuli.Abelian.ComplexAbelianPresentation (A s))
    (c : ∀ s, OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) V)
    (hc : ∀ s, (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) ∈ (c s).source ∧ c s 1 = 0 ∧
      ContMDiffOn (𝓘(ℂ, abelianSchemeNativeModel (A s))) (𝓘(ℂ, V)) 1 (c s) (c s).source ∧
      ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, abelianSchemeNativeModel (A s))) 1 (c s).symm (c s).target)
    (n : ℕ) (r : S → (Fin n → ℝ) ≃L[ℝ] V)
    (hb : ∀ s, ∃ b : Module.Basis (Fin n) ℤ (ChartPeriodLattice.Abelian.chartPeriodLattice (E := abelianSchemeNativeModel (A s)) (c s)),
      ∀ i, (b i : V) = r s (Pi.single i 1))
    (s₀ : S) (hr : ContinuousAt (fun s => (r s).toContinuousLinearMap) s₀) :
    ∃ (d : ℕ) (e : V ≃L[ℂ] (Fin d → ℂ))
      (T : ∀ s, V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)
      (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) (P s).variety),
      (∀ s v, T s v = mfderiv (𝓘(ℝ, abelianSchemeNativeModel (A s))) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P s).comparison.hom) 1 (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := abelianSchemeNativeModel (A s)) (c s) v)) ∧
      (∀ s i, (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety) = T s (r s (Pi.single i 1))) ∧
      ContinuousAt (fun s =>
        ((((T s).symm.trans e).toLinearEquiv.toLinearMap).comp
          (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀ := by
  choose T hT hmem hmark using fun s =>
    StandardModuli.Abelian.ComplexAbelianPresentation.exists_chart_period_comparison (P s) (c s)
      (hc s).1 (hc s).2.1 (hc s).2.2.1 (hc s).2.2.2
  choose b₀ hb₀ using hb
  choose b hbm using fun s => hmark s (b₀ s)
  have hb' (s : S) (i : Fin n) :
      (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety) = T s (r s (Pi.single i 1)) :=
    (hbm s i).trans (congrArg (T s) (hb₀ s i))
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective (T s₀).toLinearMap (T s₀).injective
  let d := Module.finrank ℂ V
  let e : V ≃L[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  refine ⟨d, e, T, b, hT, hb', ?_⟩
  apply PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.continuousAt_period_map_of_vectors
  intro i
  have hcol : ContinuousAt (fun s => r s (Pi.single i 1)) s₀ := hr.clm_apply continuousAt_const
  have h := e.continuous.continuousAt.comp hcol
  convert h using 1
  funext s
  change e ((T s).symm (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)) = e (r s (Pi.single i 1))
  rw [hb', ContinuousLinearEquiv.symm_apply_apply]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian
