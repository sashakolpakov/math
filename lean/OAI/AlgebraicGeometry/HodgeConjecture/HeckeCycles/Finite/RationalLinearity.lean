import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Rational Linearity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalLinearity.CM

noncomputable section

/-! Continuity extends rational scalar linearity to finite-adele scalar
linearity, because the diagonal rationals are dense in the finite adeles. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
theorem scalar (T : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hT : Continuous T)
    (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : T (a • x) = a • T x := by
  have he : (fun b : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => T (b • x)) = (fun b : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => b • T x) := by
    apply RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.denseRange_rational_finiteAdele.equalizer
      (hT.comp (continuous_id.smul continuous_const)) (continuous_id.smul continuous_const)
    funext r
    change T (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf r • x) = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf r • T x
    rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul, map_smul]
  exact congrFun he a

def linearMap (T : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hT : Continuous T) :
    (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun := T
  map_add' := T.map_add
  map_smul' := scalar T hT

def linearEquiv (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[ℚ] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toLinearEquiv :=
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := scalar e.toLinearMap e.continuous }
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

def matrix (T : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hT : Continuous T) : Matrix J I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  LinearMap.toMatrix' (linearMap T hT)

omit [Fintype J] in
theorem matrix_apply (T : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hT : Continuous T) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (matrix T hT) *ᵥ x = T x := LinearMap.toMatrix'_mulVec (linearMap T hT) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalLinearity.CM
