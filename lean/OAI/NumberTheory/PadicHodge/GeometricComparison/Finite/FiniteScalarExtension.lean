import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Finite Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension.ScalarExtension

noncomputable section

/-! Finite dimensionality descends along a genuine extension of coefficient fields. -/

open scoped TensorProduct

variable (R S : Type*) [Field R] [Field S] [Algebra R S]
  (V : Type*) [AddCommGroup V] [Module R V]

theorem finite_of_baseChange [FiniteDimensional S (S ⊗[R] V)] : FiniteDimensional R V := by
  apply Module.rank_lt_aleph0_iff.mp
  have h : Module.rank S (S ⊗[R] V) < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr inferInstance
  simpa only [Module.rank_baseChange, Cardinal.lift_lt_aleph0] using h

theorem finite_of_comparison {W : Type*} [AddCommGroup W] [Module S W]
    [FiniteDimensional S W] (e : (S ⊗[R] V) ≃ₗ[S] W) : FiniteDimensional R V := by
  let : FiniteDimensional S (S ⊗[R] V) := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact finite_of_baseChange R S V

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension.ScalarExtension
