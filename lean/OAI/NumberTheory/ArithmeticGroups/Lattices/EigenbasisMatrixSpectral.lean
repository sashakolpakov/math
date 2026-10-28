import OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralScaling
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization

/-! # Eigenbasis Matrix Spectral -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction

noncomputable section

/-! Spectral changes in a fixed eigenbasis, in concrete matrix form. -/

open scoped Classical

def eigenbasisMatrixUnit {k : Type} [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix.GeneralLinearGroup (Fin n) k :=
  let c := Pi.basisFun k (Fin n)
  ⟨c.toMatrix b, b.toMatrix c, c.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip c⟩

theorem matrix_eq_eigenbasis_conjugate
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k)
    (hb : ∀ i, Matrix.toLin' A (b i) = w i • b i) :
    A = (eigenbasisMatrixUnit b).val * Matrix.diagonal w * ((eigenbasisMatrixUnit b)⁻¹).val := by
  have hd : LinearMap.toMatrix b b (Matrix.toLin' A) = Matrix.diagonal w := by
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, hij]
  change A = (Pi.basisFun k (Fin n)).toMatrix b * Matrix.diagonal w *
    b.toMatrix (Pi.basisFun k (Fin n))
  rw [← hd, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact (LinearMap.toMatrix_toLin _ _ A).symm

def eigenbasisSpectralMatrix {k : Type} [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  LinearMap.toMatrix' (Matrix.toLin b b (Matrix.diagonal w))

theorem eigenbasisSpectralMatrix_apply
    {k : Type} [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k) (i : Fin n) :
    Matrix.toLin' (eigenbasisSpectralMatrix b w) (b i) = w i • b i := by
  rw [eigenbasisSpectralMatrix, Matrix.toLin'_toMatrix']
  exact Module.End.mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal w i b).1

theorem infinitesimal_eigenbasis_spectral_matrix
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (b : Module.Basis (Fin n) k (Fin n → k)) (S : Matrix (Fin n) (Fin n) k)
    (w : Fin n → k) (ψ : k →+ k)
    (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i)
    (hmem : S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    eigenbasisSpectralMatrix b (fun i => ψ (w i)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  rw [matrix_eq_eigenbasis_conjugate _ b _ (eigenbasisSpectralMatrix_apply b _)]
  apply AdditiveSpectralAction.Construction.infinitesimal_additive_spectral_matrix G (eigenbasisMatrixUnit b) w ψ
  rwa [← matrix_eq_eigenbasis_conjugate S b w hS]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral.Construction
