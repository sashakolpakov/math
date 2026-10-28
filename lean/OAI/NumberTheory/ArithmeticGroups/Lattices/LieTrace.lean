import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Perfect

/-! # Lie Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LieTrace.Construction

noncomputable section

/-! Every finite-dimensional representation of the infinitesimal Lie
algebra of an Lattices group has trace zero, over any extension field. -/

attribute [local instance] LieRing.ofAssociativeRing

theorem perfectLie_trace_representation_zero
    {k L V : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    (h : LieAlgebra.derivedSeries k L 1 = ⊤)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : L →ₗ⁅k⁆ Module.End k V) (x : L) : LinearMap.trace k V (ρ x) = 0 := by
  let f : L →ₗ[k] k := (LinearMap.trace k V).comp ρ.toLinearMap
  have hker : (LieAlgebra.derivedSeries k L 1 : Submodule k L) ≤ f.ker := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    change LinearMap.trace k V (ρ ⁅a, b⁆) = 0
    rw [ρ.map_lie, LinearMap.trace_lie]
  rw [h] at hker
  exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule k L))

theorem arithmetic_infinitesimal_trace_zero
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) →ₗ⁅K⁆ Module.End K V)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) :
    LinearMap.trace K V (ρ A) = 0 :=
  perfectLie_trace_representation_zero (Infinitesimal.Perfect.Construction.infinitesimal_baseChange_derived_eq_top G hconn hsemi) ρ A

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LieTrace.Construction
