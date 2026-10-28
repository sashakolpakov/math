import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartLatticeAction

/-! # Chart Endomorphism Exponential -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChartEndomorphismExponential

noncomputable section

/-! Actual endomorphisms commute with their derivatives in chart
exponential coordinates. Equality of matrices intertwines real frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral A.scheme.left] [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "L" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)
local instance chartEndomorphismExponential_nativeRealLieGroup :
    LieGroup (𝓘(ℝ, L)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup A.scheme

theorem nativeChartDerivative_exp
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (k : A.scheme ⟶ A.scheme) [IsMonHom k] (D : V →L[ℝ] V)
    (hD : ∀ v, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c (D v) =
      mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) 1
        (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c v)) (v : V) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L) c v) =
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L) c (D v) := by
  let f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme :=
    { toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k
      map_one' := MonObj.one_comp k
      map_mul' := fun x y => MonObj.mul_comp x y k }
  have hf : MDifferentiable (𝓘(ℝ, L)) (𝓘(ℝ, L)) f :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map k 1).mdifferentiable (by simp)
  exact (ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality.Abelian.groupMap_exp f hf (show GroupLieAlgebra (𝓘(ℝ, L)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)
    from ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) c v)).trans (congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)) (hD v).symm)

theorem conjugatedMatrices_intertwine {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r₀ r : W ≃L[ℝ] V) (D₀ D : V →L[ℝ] V)
    (h : ∀ u, r.symm (D (r u)) = r₀.symm (D₀ (r₀ u))) (v : V) :
    D (r (r₀.symm v)) = r (r₀.symm (D₀ v)) := by
  apply r.symm.injective
  rw [r.symm_apply_apply, h, r₀.apply_symm_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.ChartEndomorphismExponential
