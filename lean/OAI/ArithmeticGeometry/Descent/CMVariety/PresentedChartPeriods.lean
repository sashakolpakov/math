import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation
import OAI.ArithmeticGeometry.Descent.CMVariety.ComplexChartTangents
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Presented Chart Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PresentedChartPeriods.Abelian

noncomputable section

/-!
Transport of the constructed chart periods through an actual geometric
abelian-fiber presentation. The resulting marking is a basis of the
presentation's genuine native period lattice.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

def latticeEquivOfMemIff {V W : Type*}
    [AddCommGroup V] [AddCommGroup W]
    (T : V ≃ₗ[ℤ] W) (Λ : Submodule ℤ V) (Γ : Submodule ℤ W)
    (h : ∀ v, T v ∈ Γ ↔ v ∈ Λ) : Λ ≃ₗ[ℤ] Γ :=
  T.ofSubmodules Λ Γ (by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h v).mpr hv
    · intro hw
      refine ⟨T.symm w, ?_, T.apply_symm_apply w⟩
      exact (h (T.symm w)).mp (by simpa using hw))

namespace ComplexAbelianPresentation

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral A.scheme.left] [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)

local instance : LieGroup (𝓘(ℝ, ModelA)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :=
  IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup A.scheme

/-- Complex tangent coordinates carry the literal chart lattice onto
the actual abelian variety's period lattice, with an exact basis formula. -/
theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.exists_chart_period_comparison
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (h1 : (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) ∈ c.source) (h0 : c 1 = 0)
    (hc : ContMDiffOn (𝓘(ℂ, ModelA)) (𝓘(ℂ, V)) 1 c c.source)
    (hi : ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, ModelA)) 1 c.symm c.target) :
    ∃ T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety,
      (∀ v, T v = mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1 (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c v)) ∧
      (∀ v, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety ↔ v ∈ ChartPeriodLattice.Abelian.chartPeriodLattice (E := ModelA) c) ∧
      ∀ {Index : Type} (b : Module.Basis Index ℤ (ChartPeriodLattice.Abelian.chartPeriodLattice (E := ModelA) c)),
        ∃ b' : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index P.variety,
          ∀ i, (b' i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety) = T (b i : V) := by
  let : IsIntegral P.variety.toOver.left := P.variety.variety.property
  let : Smooth P.variety.toOver.hom := P.variety.variety.presentation.smooth
  let : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) :=
    P.variety.variety.presentation.complexPoints_t2Space
  let : IsMonHom P.comparison.hom := P.comparison_group
  obtain ⟨Tc, hTc⟩ := ComplexChartTangents.Abelian.exists_complex_chart_tangent_equiv c h1 h0 hc hi
  let T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety := Tc.trans (IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent P.comparison)
  have hcv (v : V) : ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c v = Tc v :=
    congrArg (fun D : V →L[ℝ] ModelA => D v) hTc
  have hm (v : V) : T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety ↔ v ∈ ChartPeriodLattice.Abelian.chartPeriodLattice (E := ModelA) c := by
    have h := IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_mem_lattice_iff P.comparison (Tc v)
    change T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety ↔
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) (Tc v) = 1 at h
    apply h.trans
    change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) (Tc v) = 1 ↔
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c v) = 1
    rw [hcv]
  refine ⟨T, ?_, hm, ?_⟩
  · intro v
    have he := congrArg (fun D : ModelA →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety => D (Tc v))
      (IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_real P.comparison)
    exact he.symm.trans (congrArg
      (fun w : ModelA => mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1 w) (hcv v).symm)
  · intro Index b
    let e := latticeEquivOfMemIff (T.toLinearEquiv.restrictScalars ℤ)
      (ChartPeriodLattice.Abelian.chartPeriodLattice (E := ModelA) c) (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety) hm
    exact ⟨b.map e, fun _ => rfl⟩

end ComplexAbelianPresentation

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PresentedChartPeriods.Abelian
