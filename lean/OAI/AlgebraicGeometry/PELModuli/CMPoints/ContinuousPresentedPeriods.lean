import OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Continuous Presented Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousPresentedPeriods

noncomputable section

section

/-! Full continuous chart markings give continuous native period matrices
and canonical H1 frames on the same open neighborhood. The chosen native
presentations need no additional continuity assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {S V : Type} [TopologicalSpace S]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
  {g : ℕ} (A : S → AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  [∀ s, IsIntegral (A s).scheme.left] [∀ s, T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme)]

local instance (s : S) : LieGroup (𝓘(ℝ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) ∞
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) := ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (A s).scheme

theorem exists_continuousOn_presented_periods
    (P : ∀ s, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (A s))
    (c : ∀ s, OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) V)
    (hc : ∀ s, (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) ∈ (c s).source ∧ c s 1 = 0 ∧
      ContMDiffOn (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) (𝓘(ℂ, V)) 1 (c s) (c s).source ∧
      ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) 1 (c s).symm (c s).target)
    (n : ℕ) (r : S → (Fin n → ℝ) ≃L[ℝ] V)
    (hb : ∀ s, ∃ b : Module.Basis (Fin n) ℤ
        (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)) (c s)),
      ∀ i, (b i : V) = r s (Pi.single i 1))
    (U : Set S) (hU : IsOpen U) (s₀ : S) (hs₀ : s₀ ∈ U)
    (hr : ContinuousOn (fun s => (r s).toContinuousLinearMap) U) :
    ∃ (d : ℕ) (e : V ≃L[ℂ] (Fin d → ℂ))
      (T : ∀ s, V ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)
      (b : ∀ s, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) (P s).variety),
      (∀ s v, T s v = mfderiv (𝓘(ℝ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)))
        (𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P s).comparison.hom) 1
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)) (c s) v)) ∧
      (∀ s i, (b s i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety) = T s (r s (Pi.single i 1))) ∧
      ContinuousOn (fun s =>
        ((((T s).symm.trans e).toLinearEquiv.toLinearMap).comp
          (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) U := by
  obtain ⟨d, e, T, b, hT, hbm, _⟩ := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.exists_continuous_presented_periods A P c hc n r hb s₀
    (hr.continuousAt (hU.mem_nhds hs₀))
  refine ⟨d, e, T, b, hT, hbm, ?_⟩
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ArithmeticGeometry.Descent.CMVariety.PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.continuousAt_period_map_of_vectors
  intro i
  have hcol : ContinuousAt (fun q => r q (Pi.single i 1)) s :=
    (hr.continuousAt (hU.mem_nhds hs)).clm_apply continuousAt_const
  have h := e.continuous.continuousAt.comp hcol
  convert h using 1
  funext q
  change e ((T q).symm (b q i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety)) = e (r q (Pi.single i 1))
  rw [hbm, ContinuousLinearEquiv.symm_apply_apply]

theorem continuousOn_native_hodge_frames
    {I J S : Type} [Fintype I] [Fintype J] [TopologicalSpace S]
    (B : S → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking I (B s))
    (e : ∀ s, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (B s) ≃ₗ[ℂ] (J → ℂ))
    (H : ∀ s, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((B s).variety.rationalCohomology 1))
    (hH : ∀ s, HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 (B s).variety (H s))
    (U : Set S)
    (hp : ContinuousOn (fun s =>
      ((e s).toLinearMap.comp (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) U) :
    ContinuousOn (fun s => ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods.periodTranspose
      ((e s).toLinearMap.comp (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) U ∧
    ∀ s, (ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods.periodTranspose
      ((e s).toLinearMap.comp (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap).toLinearMap.range =
        (ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s) (H s)).holomorphic.map
          ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap := by
  exact ⟨ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods.continuous_periodTranspose.comp_continuousOn hp,
    fun s => ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_range_markedHodge (b s) (e s) (H s) (hH s)⟩

end

/-! Holomorphic basis vectors give a holomorphic matrix in fixed complex
tangent coordinates. On the supplied open set this is exactly the period
matrix of the actual native fibers, with their full integral markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {S V : Type} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
  {g : ℕ} (A : S → AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  [∀ s, IsIntegral (A s).scheme.left] [∀ s, T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme)]

local instance (s : S) : LieGroup (𝓘(ℝ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) ∞
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) := ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (A s).scheme

theorem exists_holomorphic_presented_periods_on
    (P : ∀ s, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (A s))
    (c : ∀ s, OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) V)
    (U : Set S)
    (hc : ∀ s ∈ U, (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) ∈ (c s).source ∧ c s 1 = 0 ∧
      ContMDiffOn (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) (𝓘(ℂ, V)) 1 (c s) (c s).source ∧
      ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s))) 1 (c s).symm (c s).target)
    (n : ℕ) (r : S → (Fin n → ℝ) ≃L[ℝ] V)
    (hb : ∀ s ∈ U, ∃ b : Module.Basis (Fin n) ℤ
        (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)) (c s)),
      ∀ i, (b i : V) = r s (Pi.single i 1))
    (s₀ : S) (hs₀ : s₀ ∈ U)
    (hr : ContinuousOn (fun s => (r s).toContinuousLinearMap) U)
    (hhol : ∀ i, DifferentiableOn ℂ (fun s => r s (Pi.single i 1)) U) :
    ∃ (d : ℕ) (e : V ≃L[ℂ] (Fin d → ℂ))
      (T : ∀ s : U, V ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)
      (b : ∀ s : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) (P s).variety)
      (period : S → (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∀ (s : U) v, T s v = mfderiv (𝓘(ℝ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)))
        (𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P s).comparison.hom) 1
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A s)) (c s) v)) ∧
      (∀ (s : U) i, (b s i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety) = T s (r s (Pi.single i 1))) ∧
      (∀ s : U, period s =
        ((((T s).symm.trans e).toLinearEquiv.toLinearMap).comp
          (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) ∧
      DifferentiableOn ℂ period U := by
  obtain ⟨d, e, T, b, hT, hbm, _⟩ := ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.exists_continuous_presented_periods
    (fun s : U => A s) (fun s : U => P s) (fun s : U => c s)
    (fun s : U => hc s s.property) n (fun s : U => r s)
    (fun s : U => hb s s.property) ⟨s₀, hs₀⟩ hr.domRestrict.continuousAt
  let frames := ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := Fin d → ℂ) (Fin n)
  let period := fun s : S => frames.symm (fun i => e (r s (Pi.single i 1)))
  have hdiff : DifferentiableOn ℂ period U :=
    frames.symm.differentiable.comp_differentiableOn (differentiableOn_pi.mpr
      (fun i => e.differentiable.comp_differentiableOn (hhol i)))
  refine ⟨d, e, T, b, period, hT, hbm, ?_, hdiff⟩
  intro s
  apply frames.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  change e (r s (Pi.single i 1)) =
    e ((T s).symm (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s) (Pi.single i 1)))
  have hbi : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s) (Pi.single i 1) =
      (b s i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety) := by
    simp [ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, Pi.single_apply]
  rw [hbi, hbm, ContinuousLinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousPresentedPeriods
