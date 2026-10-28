import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Support
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedParameterDimension

/-! # Isolated Pair Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedPairDimension

noncomputable section

/-! An isolated parameter fiber forces the intersection of two
finite-module supports to have dimension at most one. Every nonclosed
prime in that intersection is minimal there. -/

open _root_.CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (r : R)
  (hisolated : (Module.support R M ∩ Module.support R N) ∩
    Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R})

include hisolated

theorem dimension (hrm : r ∈ maximalIdeal R) :
    Order.krullDim ↥(Module.support R M ∩ Module.support R N) ≤ 1 := by
  have hi : Module.support R (M ⊗[R] N) ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆
      {closedPoint R} := by rwa [Tensor.Support.support]
  have h := IsolatedParameterDimension.dimension R (.of R (M ⊗[R] N)) r hi hrm
  change Order.krullDim (Module.support R (M ⊗[R] N)) ≤ 1 at h
  rwa [Tensor.Support.support] at h

theorem minimal (hrm : r ∈ maximalIdeal R) (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M ∩ Module.support R N) (hne : p ≠ closedPoint R)
    (q : PrimeSpectrum R) (hq : q ∈ Module.support R M ∩ Module.support R N)
    (hqp : q.asIdeal ≤ p.asIdeal) : q = p := by
  have hi : Module.support R (M ⊗[R] N) ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆
      {closedPoint R} := by rwa [Tensor.Support.support]
  apply IsolatedParameterDimension.minimal R (.of R (M ⊗[R] N)) r hi hrm p _ hne q _ hqp
  · rwa [Tensor.Support.support]
  · rwa [Tensor.Support.support]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedPairDimension
