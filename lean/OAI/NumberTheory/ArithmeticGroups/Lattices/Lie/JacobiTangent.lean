import OAI.NumberTheory.ArithmeticGroups.Lattices.JacobiLinearization
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.DerivationDefect

/-! # Jacobi Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.JacobiTangent.Construction

noncomputable section

/-! At a Lie algebra with nondegenerate Killing form, every
alternating solution of the linearized Jacobi equations arises
from an infinitesimal change of basis. -/

open LieModule.Cohomology

attribute [local instance] LieRing.ofAssociativeRing

theorem lieDerivationDefect_eq_negative_coboundary
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] (T : L →ₗ[k] L) :
    DerivationDefect.Construction.lieDerivationDefect k L T = (d₁₂ k L L (-T)).val := by
  ext x y
  change T ⁅x, y⁆ - ⁅T x, y⁆ - ⁅x, T y⁆ =
    ⁅x, -T y⁆ - ⁅y, -T x⁆ - -T ⁅x, y⁆
  rw [lie_neg, lie_neg, ← lie_skew y (T x)]
  abel

theorem lieDerivationDefect_jacobiLinearization
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] (T : L →ₗ[k] L) :
    JacobiLinearization.Construction.jacobiLinearization (LieAlgebra.ad k L).toLinearMap (DerivationDefect.Construction.lieDerivationDefect k L T) = 0 := by
  rw [lieDerivationDefect_eq_negative_coboundary, JacobiLinearization.Construction.jacobiLinearization_eq_coboundary]
  exact congrArg (fun f => (f : (L →ₗ[k] L) →ₗ[k] L →ₗ[k] L →ₗ[k] L →ₗ[k] L) (-T))
    (d₂₃_comp_d₁₂ k L L)

theorem killing_jacobi_tangent_is_derivationDefect
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (hK : (killingForm k L).Nondegenerate) (C : L →ₗ[k] L →ₗ[k] L)
    (hAlt : ∀ x, C x x = 0)
    (hJac : JacobiLinearization.Construction.jacobiLinearization (LieAlgebra.ad k L).toLinearMap C = 0) :
    ∃ T : L →ₗ[k] L, DerivationDefect.Construction.lieDerivationDefect k L T = C := by
  let c : twoCochain k L L := ⟨C, hAlt⟩
  have hc : c ∈ (d₂₃ k L L).ker := by
    rw [LinearMap.mem_ker, ← JacobiLinearization.Construction.jacobiLinearization_eq_coboundary]
    exact hJac
  obtain ⟨T, hT⟩ := KillingCocycleContraction.Construction.killing_twoCocycle_is_coboundary hK ⟨c, hc⟩
  refine ⟨-T, ?_⟩
  rw [lieDerivationDefect_eq_negative_coboundary, neg_neg, hT]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.JacobiTangent.Construction
