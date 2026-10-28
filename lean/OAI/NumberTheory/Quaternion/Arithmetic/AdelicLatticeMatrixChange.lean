import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicEq

/-! # Adelic Lattice Matrix Change -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMatrixChange

noncomputable section

/-! Integral adelic automorphisms fix the standard rational lattice.
Right multiplication by a rational matrix changes the lattice by the
corresponding rational linear map. -/

open scoped Classical _root_.NumberField _root_.Matrix

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteAdelicMatrixLattice_integral_unit_eq_standard
    (A : (Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F))ˣ)
    (hA : ∀ i j, A.val i j ∈ ScalarApproximation.integralScalarAdeles F)
    (hAi : ∀ i j, A.inv i j ∈ ScalarApproximation.integralScalarAdeles F) :
    FiniteAdelicLattice.finiteAdelicMatrixLattice A.val = (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module := by
  rw [← FiniteAdelicEq.finiteAdelicMatrixLattice_one_eq_standard]
  ext x
  change (A.val *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x ∈ FiniteAdelicLattice.integralFiniteAdelicVectors n) ↔
    (1 : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x ∈ FiniteAdelicLattice.integralFiniteAdelicVectors n
  rw [Matrix.one_mulVec]
  constructor
  · intro hx
    have h := FiniteAdelicLattice.integralFiniteAdelicVectors_mulVec A.inv hAi (A.val *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) hx
    rw [Matrix.mulVec_mulVec, A.inv_val, Matrix.one_mulVec] at h
    exact h
  · exact FiniteAdelicLattice.integralFiniteAdelicVectors_mulVec A.val hA _

theorem finiteAdelicMatrix_mul_rational_vector
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) (B : Matrix (Fin n) (Fin n) F) (x : Fin n → F) :
    (A * B.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))) *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x =
      A *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n (B *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext i
  exact (RingHom.map_mulVec (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) B x i).symm

theorem finiteAdelicMatrixLattice_mul_rational
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) (B : Matrix (Fin n) (Fin n) F) :
    FiniteAdelicLattice.finiteAdelicMatrixLattice (A * B.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))) =
      (FiniteAdelicLattice.finiteAdelicMatrixLattice A).comap (B.mulVecLin.restrictScalars (𝓞 F)) := by
  ext x
  change ((A * B.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))) *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x ∈
      FiniteAdelicLattice.integralFiniteAdelicVectors n) ↔
    (A *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n (B *ᵥ x) ∈ FiniteAdelicLattice.integralFiniteAdelicVectors n)
  rw [finiteAdelicMatrix_mul_rational_vector]

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMatrixChange
