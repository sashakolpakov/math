import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteReduction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticHeightDescent
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Height Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HeightDescent.Construction

noncomputable section

/-! The remaining geometric height, once constructed, supplies the actual endomorphism rank bound.
No height or finite-dimensionality assertion is included in the native Completion hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- One of 2 and 3 is invertible in every field. -/
theorem exists_nonzero_natCast_ge_two (K : Type u) [Field K] :
    ∃ n : ℕ, 2 ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h2 : (2 : K) ≠ 0
  · exact ⟨2, le_rfl, h2⟩
  · refine ⟨3, by omega, ?_⟩
    have h2' : (2 : K) = 0 := not_ne_iff.mp h2
    have h3 : (3 : K) = 1 := by calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2', zero_add]
    norm_num only [Nat.cast_ofNat]
    rw [h3]
    exact one_ne_zero

/-- Arithmetic descent uses the proved finite reductions of the actual endomorphism group. -/
theorem algebraicEnd_finiteGenerated_of_discrete_quadratic_height
    (h : QuadraticHeightDescent.Construction.DiscreteQuadraticHeight (Endomorphisms.Construction.AlgebraicEnd A)) : AddGroup.FG (Endomorphisms.Construction.AlgebraicEnd A) := by
  obtain ⟨n, hn, hnK⟩ := exists_nonzero_natCast_ge_two K
  apply h.finiteGenerated_of_finite_reductions n hn
  intro r
  exact FiniteReduction.Construction.algebraicEnd_quotient_nsmul_finite A (n ^ r) (by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hnK)

/-- A discrete positive geometric quadratic height would make the genuine rational
endomorphism algebra finite-dimensional. The height itself remains to be constructed. -/
theorem rationalAlgebraicEnd_finiteDimensional_of_discrete_quadratic_height
    (h : QuadraticHeightDescent.Construction.DiscreteQuadraticHeight (Endomorphisms.Construction.AlgebraicEnd A)) :
    FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) := by
  have : Module.Finite ℤ (Endomorphisms.Construction.AlgebraicEnd A) :=
    Module.Finite.iff_addGroup_fg.mpr (algebraicEnd_finiteGenerated_of_discrete_quadratic_height A h)
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HeightDescent.Construction
