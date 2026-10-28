import OAI.ArithmeticGeometry.Descent.CMVariety.FixedEnhancementRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyRigidity

/-! # Fixed Enhancement Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FixedEnhancementPeriods.Abelian.IntrinsicPeriods

noncomputable section

/-! Period and derivative rigidity for the explicit CM tuple chosen before spreading. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

variable {S Index : Type} [TopologicalSpace S] [Fintype Index]

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem fixed_enhancement_continuous_period_matrices_rigid
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S) (E : AlgebraicEnhancement.Abelian.CMEnhancement (A s₀))
    (hperiod : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀)
    (k : ∀ s, Fin E.size → ((A s).toOver ⟶ (A s).toOver))
    (hk : ∀ s i, IsMonHom (k s i)) (hk₀ : ∀ i, k s₀ i = E.map i)
    (hmatrix : ∀ l i j, ContinuousAt
      (fun s => (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s l) ((Pi.basisFun ℚ Index) i) j : ℝ)) s₀) :
    ∀ᶠ s in 𝓝 s₀, EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) E.map (k s) := by
  let frame := fun s => MarkedActions.Abelian.IntrinsicPeriods.periodTranspose
    (((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap)
  have hframe (s : S) : (frame s).toLinearMap.range =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))).holomorphic.map
        MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap :=
    MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_range_markedHodge (b s) (e s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))
      (Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s))
  let W := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s₀))).antiholomorphic.map
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap
  have hcompl : IsCompl (frame s₀).toLinearMap.range W := by
    rw [hframe s₀]
    exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s₀))).complementary
  have hcont : ContinuousAt frame s₀ := MarkedActions.Abelian.IntrinsicPeriods.continuous_periodTranspose.continuousAt.comp hperiod
  have hinj : Function.Injective (frame s₀) := MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_injective _
    ((e s₀).surjective.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap_surjective (b s₀)))
  have hneigh := PeriodTransversality.Abelian.eventually_isCompl_range frame s₀ hcont W hinj hcompl
  have hconstant : ∀ᶠ s in 𝓝 s₀, ∀ i,
      MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (E.map i) := by
    rw [Filter.eventually_all]
    intro i
    have h := IntegralMarkedMaps.Abelian.IntrinsicPeriods.markedEndomorphism_eventually_eq_of_continuous A b (fun s => k s i)
      (fun s => hk s i) s₀ (hmatrix i)
    simpa only [hk₀ i] using h
  filter_upwards [hneigh, hconstant] with s hs hsk
  apply FixedEnhancementRigidity.Abelian.IntrinsicPeriods.fixed_enhancement_marked_equivariant_iso E (b s₀) (A s) (b s)
    (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s)) (Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s)) (k s) (hk s)
    (fun i => (hsk i).symm)
  rw [hframe s] at hs
  exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl_iff.mpr hs

theorem fixed_enhancement_continuous_native_derivatives_rigid
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S) (E : AlgebraicEnhancement.Abelian.CMEnhancement (A s₀))
    (hperiod : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀)
    (k : ∀ s, Fin E.size → ((A s).toOver ⟶ (A s).toOver))
    (hk : ∀ s i, IsMonHom (k s i)) (hk₀ : ∀ i, k s₀ i = E.map i)
    (hderiv : ∀ l j, ContinuousAt
      (fun s => e s
        (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k s l)) (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).toOver)
            (b s j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))) s₀) :
    ∀ᶠ s in 𝓝 s₀, EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) E.map (k s) := by
  apply fixed_enhancement_continuous_period_matrices_rigid A b d e s₀ E hperiod k hk hk₀
  intro l
  apply PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.markedEndomorphism_continuous_of_lift_images A b d e (fun s => k s l)
    (fun s => hk s l) s₀
  · exact PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.realPeriodInCoordinates_continuousAt A b d e s₀ hperiod
  · dsimp only
    let (s : S) : IsMonHom (k s l) := hk s l
    intro j
    convert hderiv l j using 1
    ext s
    rw [LinearLiftDerivative.Abelian.IntrinsicPeriods.algebraicLinearLift_eq_mfderiv]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FixedEnhancementPeriods.Abelian.IntrinsicPeriods
