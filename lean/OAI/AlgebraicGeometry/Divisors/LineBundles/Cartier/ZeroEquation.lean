import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Zero Equation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.ZeroEquation.BundleCycles

noncomputable section

/-! # LineBundleCycles: an identically zero equation gives the zero Cartier point map -/

open _root_.AlgebraicGeometry

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]

theorem principalCartierPointCycle_zero_equation (W : TopologicalSpace.IrreducibleCloseds X) :
    Principal.CartierCycle.BundleCycles.principalCartierPointCycle (0 : Γ(X, ⊤)) W = 0 := by
  change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W
    (((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤).hom ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop.hom 0)) = 0
  rw [map_zero, map_zero, Principal.CartierCycle.BundleCycles.schemePrincipalPointDivisor_zero]

theorem principalCartierPointMap_zero_equation (z : X →₀ ℚ) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap (0 : Γ(X, ⊤)) z = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add z w hz hw => rw [map_add, hz, hw, add_zero]
  | single x q => rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, principalCartierPointCycle_zero_equation, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.ZeroEquation.BundleCycles
