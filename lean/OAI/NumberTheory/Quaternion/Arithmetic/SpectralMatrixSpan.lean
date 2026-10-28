import OAI.NumberTheory.Quaternion.Arithmetic.IntegerSpectralSpan
import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral

/-! # Spectral Matrix Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SpectralMatrixSpan

noncomputable section

/-! A diagonalizable infinitesimal matrix is spanned by its integer
spectral changes, all of which remain in the actual algebraic Lie algebra. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction Set

variable {K : Type} [Field K] [CharZero K] {n : ℕ}

def eigenbasisSpectralLinearMap (b : Module.Basis (Fin n) K (Fin n → K)) :
    (Fin n → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b
  map_add' x y := by
    apply Matrix.toLin'.injective
    apply b.ext
    intro i
    simp only [map_add, LinearMap.add_apply, ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply, Pi.add_apply, add_smul]
  map_smul' c x := by
    apply Matrix.toLin'.injective
    apply b.ext
    intro i
    simp only [map_smul, LinearMap.smul_apply, ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply, Pi.smul_apply,
      smul_eq_mul, smul_smul, RingHom.id_apply]

theorem matrix_mem_span_integer_spectral
    (S : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K))
    (w : Fin n → K) (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i) :
    S ∈ Submodule.span K (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b '' IntegerSpectralSpan.integerSpectralVectors w) := by
  have hs : ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b w = S := by
    apply Matrix.toLin'.injective
    apply b.ext
    intro i
    exact (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply b w i).trans (hS i).symm
  have hm : eigenbasisSpectralLinearMap b w ∈
      (Submodule.span K (IntegerSpectralSpan.integerSpectralVectors w)).map (eigenbasisSpectralLinearMap b) :=
    ⟨w, IntegerSpectralSpan.finite_family_mem_integer_spectral_span w, rfl⟩
  rw [Submodule.map_span] at hm
  change ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b w ∈
    Submodule.span K (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b '' IntegerSpectralSpan.integerSpectralVectors w) at hm
  exact hs ▸ hm

omit [CharZero K] in
theorem integer_spectral_matrix_mem_infinitesimal
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) (S : Matrix (Fin n) (Fin n) K)
    (b : Module.Basis (Fin n) K (Fin n → K)) (w : Fin n → K)
    (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i) (hmem : S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {z : Fin n → K} (hz : z ∈ IntegerSpectralSpan.integerSpectralVectors w) :
    ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b z ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  obtain ⟨m, rfl, ψ, hψ⟩ := hz
  have ht := ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.infinitesimal_eigenbasis_spectral_matrix G b S w ψ hS hmem
  have he : (fun i => ψ (w i)) = fun i => (m i : K) := funext hψ
  rwa [he] at ht

omit [CharZero K] in
theorem integer_spectral_matrix_is_polynomial
    (S : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K))
    (w : Fin n → K) (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i)
    {z : Fin n → K} (hz : z ∈ IntegerSpectralSpan.integerSpectralVectors w) :
    ∃ p : Polynomial K, Polynomial.aeval S p = ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b z := by
  obtain ⟨m, rfl, ψ, hψ⟩ := hz
  have hz' (i : Fin n) : Matrix.toLin' (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b (fun i => (m i : K))) (b i) =
      ψ (w i) • b i := by rw [ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply, hψ i]
  obtain ⟨p, hp⟩ := ArithmeticGroups.Lattices.PolynomialSpectralFunctions.Construction.eigenvalue_function_is_polynomial b (Matrix.toLin' S)
    (Matrix.toLin' (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b (fun i => (m i : K)))) w ψ hS hz'
  refine ⟨p, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  rw [← Polynomial.aeval_algHom_apply]
  exact hp

omit [CharZero K] in
theorem spectral_matrix_is_polynomial_of_equal_eigenvalues
    (S : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K))
    (w u : Fin n → K) (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i)
    (hu : ∀ i j, w i = w j → u i = u j) :
    ∃ p : Polynomial K, Polynomial.aeval S p = ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b u := by
  obtain ⟨p, hp⟩ := (Polynomial.exists_eval_eq_iff w u).mpr hu
  refine ⟨p, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  rw [← Polynomial.aeval_algHom_apply]
  apply b.ext
  intro i
  change Polynomial.aeval (Matrix.toLin' S) p (b i) =
    Matrix.toLin' (ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b u) (b i)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hS i), hp i,
    ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply]

end

end OAI.NumberTheory.Quaternion.Arithmetic.SpectralMatrixSpan
