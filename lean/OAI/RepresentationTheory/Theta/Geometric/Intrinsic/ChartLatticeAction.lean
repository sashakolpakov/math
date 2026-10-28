import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Chart Lattice Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartLatticeAction

noncomputable section

/-! The derivative of an actual abelian scheme endomorphism preserves
the full native period lattice in relative chart coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral A.scheme.left] [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "L" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)
local instance : LieGroup (𝓘(ℝ, L)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup A.scheme

theorem nativeChartDerivative_preserves_lattice
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (k : A.scheme ⟶ A.scheme) [IsMonHom k]
    (D : V →L[ℝ] V)
    (hD : ∀ v, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c (D v) =
      mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) 1
        (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c v)) :
    ∀ v ∈ ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := L) c, D v ∈ ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := L) c := by
  intro v hv
  let f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme :=
    { toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k
      map_one' := MonObj.one_comp k
      map_mul' := fun x y => MonObj.mul_comp x y k }
  have hf : MDifferentiable (𝓘(ℝ, L)) (𝓘(ℝ, L)) f :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map k 1).mdifferentiable (by simp)
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c v) = 1 at hv
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c (D v)) = 1
  rw [hD]
  exact (ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality.Abelian.groupMap_exp f hf (show GroupLieAlgebra (𝓘(ℝ, L)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)
    from ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c v)).symm.trans ((congrArg f hv).trans f.map_one)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartLatticeAction
