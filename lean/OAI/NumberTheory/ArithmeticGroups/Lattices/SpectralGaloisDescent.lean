import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import Mathlib.FieldTheory.Galois.Infinite

/-! # Spectral Galois Descent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralGaloisDescent.Construction

noncomputable section

/-! Galois-equivariant functions of a matrix's eigenvalues descend to
the original coefficient field. -/

open scoped Classical
open _root_.Matrix

theorem matrix_eigenvector_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k) (a : k)
    (hx : Matrix.toLin' A x = a • x) :
    Matrix.toLin' (A.map ι) (ι ∘ x) = ι a • (ι ∘ x) := by
  funext i
  rw [Matrix.toLin'_apply, ← RingHom.map_mulVec]
  have hi := congrFun hx i
  change (A *ᵥ x) i = a * x i at hi
  simp only [hi, map_mul, Pi.smul_apply, smul_eq_mul, Function.comp_apply]

theorem matrix_spectral_function_automorphism
    {K : Type} [Field K] {n : ℕ}
    (b : Module.Basis (Fin n) K (Fin n → K))
    (S T : Matrix (Fin n) (Fin n) K) (w : Fin n → K) (ψ : K → K)
    (hS : ∀ i, Matrix.toLin' S (b i) = w i • b i)
    (hT : ∀ i, Matrix.toLin' T (b i) = ψ (w i) • b i)
    (σ : K ≃+* K) (hfix : S.map σ = S)
    (hψ : ∀ x, σ (ψ x) = ψ (σ x)) : T.map σ = T := by
  apply Matrix.toLin'.injective
  apply b.ext
  intro i
  have hfix' : S.map σ.symm = S := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) K => A.map σ.symm) hfix
    ext i j : 1
    simpa only [Matrix.map_apply, RingEquiv.symm_apply_apply] using
      (congrFun (congrFun h i) j).symm
  have hx := matrix_eigenvector_coefficient_map σ.symm.toRingHom S (b i) (w i) (hS i)
  change Matrix.toLin' (S.map σ.symm) (σ.symm ∘ b i) = σ.symm (w i) • (σ.symm ∘ b i) at hx
  rw [hfix'] at hx
  have hTx := PolynomialSpectralFunctions.Construction.eigenvalue_function_on_eigenvector b (Matrix.toLin' S) (Matrix.toLin' T)
    w ψ hS hT (σ.symm ∘ b i) (σ.symm (w i)) hx
  have hmap := matrix_eigenvector_coefficient_map σ.toRingHom T (σ.symm ∘ b i)
    (ψ (σ.symm (w i))) hTx
  change Matrix.toLin' (T.map σ) (σ ∘ (σ.symm ∘ b i)) =
    σ (ψ (σ.symm (w i))) • (σ ∘ (σ.symm ∘ b i)) at hmap
  have hvec : σ ∘ (σ.symm ∘ b i) = b i := by funext j; exact σ.apply_symm_apply _
  rw [hvec, hψ, σ.apply_symm_apply, ← hT i] at hmap
  exact hmap

theorem matrix_spectral_function_descends
    {k K : Type} [Field k] [Field K] [Algebra k K] [IsGalois k K] {n : ℕ}
    (b : Module.Basis (Fin n) K (Fin n → K))
    (S : Matrix (Fin n) (Fin n) k) (T : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) (ψ : K → K)
    (hS : ∀ i, Matrix.toLin' (S.map (algebraMap k K)) (b i) = w i • b i)
    (hT : ∀ i, Matrix.toLin' T (b i) = ψ (w i) • b i)
    (hψ : ∀ σ : K ≃ₐ[k] K, ∀ x, σ (ψ x) = ψ (σ x)) :
    ∃ T₀ : Matrix (Fin n) (Fin n) k, T₀.map (algebraMap k K) = T := by
  have hfixed (σ : K ≃ₐ[k] K) : T.map σ = T := by
    apply matrix_spectral_function_automorphism b (S.map (algebraMap k K)) T w ψ hS hT
      σ.toRingEquiv _ (hψ σ)
    ext i j : 1
    exact σ.commutes (S i j)
  have hentry (i j : Fin n) : ∃ a : k, algebraMap k K a = T i j := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (T i j)).mpr
    intro σ
    exact congrFun (congrFun (hfixed σ) i) j
  choose T₀ hT₀ using hentry
  exact ⟨T₀, Matrix.ext hT₀⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralGaloisDescent.Construction
