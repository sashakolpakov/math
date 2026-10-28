import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore

/-! # Differential Generators -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.DifferentialGenerators

/-! A family whose derivatives stay in its generated ideal lies in the
differential core whenever it vanishes at the base ideal. -/

theorem span_le_differentialCore_of_generators
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (S : Set (Derivation k A A)) (P : Set A) (I : Ideal A)
    (hP : P ⊆ I) (hD : ∀ D ∈ S, ∀ p ∈ P, D p ∈ Ideal.span P) :
    Ideal.span P ≤ ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore S I := by
  have hgen : ∀ m, P ⊆ ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.iteratedDerivativeIdeal S I m := by
    intro m
    induction m with
    | zero => exact hP
    | succ m ih =>
      intro p hp
      exact ⟨ih hp, fun D hDS => (Ideal.span_le.mpr ih) (hD D hDS p hp)⟩
  exact le_iInf (fun m => Ideal.span_le.mpr (hgen m))

end OAI.NumberTheory.Quaternion.Arithmetic.DifferentialGenerators
