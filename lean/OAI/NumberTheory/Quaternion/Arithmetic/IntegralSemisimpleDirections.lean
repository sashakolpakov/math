import OAI.NumberTheory.Quaternion.Arithmetic.SpectralMatrixSpan
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization

/-! # Integral Semisimple Directions -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralSemisimpleDirections

noncomputable section

/-! A diagonalizable algebraic infinitesimal matrix is spanned by
integrable integer-weight directions whose cocharacter values are
polynomials in that same matrix. This gives commuting Galois orbits. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization.Construction Set _root_.Matrix

variable {K : Type} [Field K] [CharZero K] {n : ℕ}

def integralPolynomialDirections (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n)
    (S : Matrix (Fin n) (Fin n) K) : Set (Matrix (Fin n) (Fin n) K) :=
  {Y | ∃ B : ArithmeticGroups.Lattices.Algebraic.SL n K, ∃ m : Fin n → ℤ,
    Y = (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => (m i : K)) *
      ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) ∧
    Y ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G ∧
    ∀ t : Kˣ, ∃ p : Polynomial K, Polynomial.aeval S p =
      (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => ((t ^ m i : Kˣ) : K)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)}

theorem diagonalizable_mem_span_integral_polynomial_directions [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) (S : Matrix (Fin n) (Fin n) K)
    (b : Module.Basis (Fin n) K (Fin n → K)) (w : Fin n → K)
    (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i) (hmem : S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    S ∈ Submodule.span K (integralPolynomialDirections G S) := by
  obtain ⟨B, hB⟩ := ArithmeticGroups.Lattices.DiagonalConjugatorNormalization.Construction.diagonal_conjugator_normalization (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisMatrixUnit b)
  apply (Submodule.span_mono (show ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b '' IntegerSpectralSpan.integerSpectralVectors w ⊆
    integralPolynomialDirections G S from ?_)) (SpectralMatrixSpan.matrix_mem_span_integer_spectral S b w hS)
  rintro Y ⟨z, hz, rfl⟩
  have hzmem := SpectralMatrixSpan.integer_spectral_matrix_mem_infinitesimal G S b w hS hmem hz
  obtain ⟨m, rfl, ψ, hψ⟩ := hz
  refine ⟨B, m, ?_, hzmem, ?_⟩
  · exact (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.matrix_eq_eigenbasis_conjugate _ b _ (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply b _)).trans (hB _).symm
  · intro t
    have hequal (i j : Fin n) (hij : w i = w j) : m i = m j := by
      apply Int.cast_injective (α := K)
      rw [← hψ i, ← hψ j, hij]
    obtain ⟨p, hp⟩ := SpectralMatrixSpan.spectral_matrix_is_polynomial_of_equal_eigenvalues S b w
      (fun i => ((t ^ m i : Kˣ) : K)) hS (fun i j hij => by rw [hequal i j hij])
    refine ⟨p, hp.trans ?_⟩
    exact (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.matrix_eq_eigenbasis_conjugate _ b _ (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply b _)).trans (hB _).symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralSemisimpleDirections
