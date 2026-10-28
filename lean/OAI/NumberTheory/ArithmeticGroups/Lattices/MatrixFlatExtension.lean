import Mathlib

/-! # Matrix Flat Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension.Construction

noncomputable section

section

/-! Extension of scalars commutes with intersections of vector
subspaces. -/

open scoped Classical TensorProduct

variable {k K V W U : Type*} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

theorem submodule_baseChange_ker (f : V →ₗ[k] W) :
    (f.ker).baseChange K = (f.baseChange K).ker := by
  exact (Module.Flat.ker_lTensor_eq (S := K) K f).symm

theorem baseChange_prod_apply (f : V →ₗ[k] W) (g : V →ₗ[k] U) (x : K ⊗[k] V) :
    TensorProduct.prodRight k K K W U ((f.prod g).baseChange K x) =
      (f.baseChange K x, g.baseChange K x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp
  | add x y hx hy => simp [hx, hy]

theorem baseChange_prod_ker (f : V →ₗ[k] W) (g : V →ₗ[k] U) :
    ((f.prod g).baseChange K).ker = (f.baseChange K).ker ⊓ (g.baseChange K).ker := by
  ext x
  change ((f.prod g).baseChange K x = 0) ↔ f.baseChange K x = 0 ∧ g.baseChange K x = 0
  rw [← (TensorProduct.prodRight k K K W U).injective.eq_iff, map_zero, baseChange_prod_apply]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂

theorem submodule_baseChange_inf (P Q : Submodule k V) :
    (P ⊓ Q).baseChange K = P.baseChange K ⊓ Q.baseChange K := by
  have hker : (P.mkQ.prod Q.mkQ).ker = P ⊓ Q := by
    rw [LinearMap.ker_prod, P.ker_mkQ, Q.ker_mkQ]
  rw [← hker, submodule_baseChange_ker, baseChange_prod_ker,
    ← submodule_baseChange_ker, ← submodule_baseChange_ker, P.ker_mkQ, Q.ker_mkQ]

end

section

/-! The concrete identification of scalar-extended matrix spaces. -/

open scoped Classical TensorProduct

def matrixScalarExtension {k K : Type} [Field k] [Field K] [Algebra k K] (n : ℕ) :
    K ⊗[k] Matrix (Fin n) (Fin n) k ≃ₗ[K] Matrix (Fin n) (Fin n) K :=
  (TensorProduct.piRight k K K (fun _ : Fin n => Fin n → k)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piScalarRight k K K (Fin n))

theorem matrixScalarExtension_tmul
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (a : K) (A : Matrix (Fin n) (Fin n) k) :
    matrixScalarExtension n (a ⊗ₜ[k] A) = a • A.map (algebraMap k K) := by
  ext i j
  change A i j • a = a * algebraMap k K (A i j)
  rw [Algebra.smul_def, mul_comm]

def matrixSubspaceExtension
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  (W.baseChange K).map (matrixScalarExtension n).toLinearMap

theorem matrixSubspaceExtension_eq_span
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    matrixSubspaceExtension (K := K) W =
      Submodule.span K ((fun A : Matrix (Fin n) (Fin n) k => A.map (algebraMap k K)) '' W) := by
  unfold matrixSubspaceExtension
  conv_lhs => rw [← Submodule.span_eq W]
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  congr 1
  congr 1
  funext A
  exact (matrixScalarExtension_tmul (1 : K) A).trans (one_smul K _)

end

section

/-! Matrix scalar extension over a commutative coefficient algebra,
including the Minkowski algebra, need not be a field extension. -/

open scoped Classical TensorProduct

def matrixAlgebraExtension
    {k R : Type} [Field k] [CommRing R] [Algebra k R] (n : ℕ) :
    R ⊗[k] Matrix (Fin n) (Fin n) k ≃ₗ[R] Matrix (Fin n) (Fin n) R :=
  (TensorProduct.piRight k R R (fun _ : Fin n => Fin n → k)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piScalarRight k R R (Fin n))

theorem matrixAlgebraExtension_tmul
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (a : R) (A : Matrix (Fin n) (Fin n) k) :
    matrixAlgebraExtension n (a ⊗ₜ[k] A) = a • A.map (algebraMap k R) := by
  ext i j : 1
  change A i j • a = a * algebraMap k R (A i j)
  rw [Algebra.smul_def, mul_comm]

def matrixSubmoduleAlgebraExtension
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Submodule R (Matrix (Fin n) (Fin n) R) :=
  (W.baseChange R).map (matrixAlgebraExtension n).toLinearMap

theorem matrixSubmoduleAlgebraExtension_eq_span
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    matrixSubmoduleAlgebraExtension (R := R) W =
      Submodule.span R ((fun A : Matrix (Fin n) (Fin n) k => A.map (algebraMap k R)) '' W) := by
  unfold matrixSubmoduleAlgebraExtension
  conv_lhs => rw [← Submodule.span_eq W]
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  congr 1
  congr 1
  funext A
  exact (matrixAlgebraExtension_tmul (1 : R) A).trans (one_smul R _)

theorem algebraExtension_kernel
    {k R V W : Type*} [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) : (f.ker).baseChange R = (f.baseChange R).ker := by
  exact (Module.Flat.ker_lTensor_eq (S := R) R f).symm

end

/-! Finite matrix linear systems extend to a coefficient algebra and
their kernels are exactly the extended rational solution spaces. -/

open scoped Classical TensorProduct

def matrixLinearSystemExtension
    {k R ι : Type} [Field k] [CommRing R] [Algebra k R] [Fintype ι] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k)) :
    Matrix (Fin n) (Fin n) R →ₗ[R] (ι → R) :=
  (TensorProduct.piScalarRight k R R ι).toLinearMap.comp
    ((f.baseChange R).comp (matrixAlgebraExtension n).symm.toLinearMap)

theorem matrixLinearSystemExtension_tmul
    {k R ι : Type} [Field k] [CommRing R] [Algebra k R] [Fintype ι] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k)) (a : R)
    (A : Matrix (Fin n) (Fin n) k) :
    matrixLinearSystemExtension f (matrixAlgebraExtension n (a ⊗ₜ[k] A)) =
      fun i => a * algebraMap k R (f A i) := by
  change TensorProduct.piScalarRight k R R ι
    (f.baseChange R ((matrixAlgebraExtension n).symm (matrixAlgebraExtension n (a ⊗ₜ[k] A)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  funext i
  change f A i • a = a * algebraMap k R (f A i)
  rw [Algebra.smul_def, mul_comm]

theorem matrixLinearSystemExtension_base_matrix
    {k R ι : Type} [Field k] [CommRing R] [Algebra k R] [Fintype ι] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k)) (A : Matrix (Fin n) (Fin n) k) :
    matrixLinearSystemExtension (R := R) f (A.map (algebraMap k R)) =
      fun i => algebraMap k R (f A i) := by
  have h := matrixLinearSystemExtension_tmul f (1 : R) A
  simpa only [matrixAlgebraExtension_tmul, one_smul, one_mul] using h

theorem matrixLinearSystemExtension_kernel
    {k R ι : Type} [Field k] [CommRing R] [Algebra k R] [Fintype ι] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k)) :
    matrixSubmoduleAlgebraExtension (R := R) f.ker = (matrixLinearSystemExtension (R := R) f).ker := by
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [algebraExtension_kernel] at hx
    change TensorProduct.piScalarRight k R R ι
      (f.baseChange R ((matrixAlgebraExtension n).symm (matrixAlgebraExtension n x))) = 0
    rw [LinearEquiv.symm_apply_apply, hx, map_zero]
  · intro hA
    refine ⟨(matrixAlgebraExtension n).symm A, ?_, (matrixAlgebraExtension n).apply_symm_apply A⟩
    rw [algebraExtension_kernel]
    apply (TensorProduct.piScalarRight k R R ι).injective
    rw [map_zero]
    exact hA

theorem matrixLinearSystemExtension_coefficient_map
    {k R S ι : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Fintype ι] {n : ℕ} (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k))
    (ψ : R →ₐ[k] S) (A : Matrix (Fin n) (Fin n) R) :
    matrixLinearSystemExtension f (A.map ψ) = fun i => ψ (matrixLinearSystemExtension f A i) := by
  obtain ⟨x, rfl⟩ := (matrixAlgebraExtension (k := k) (R := R) n).surjective A
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, Matrix.map_add ψ ψ.map_add, map_add, hx, hy]
    funext i
    simp only [Pi.add_apply, map_add]
  | tmul a B =>
    have hm : (matrixAlgebraExtension n (a ⊗ₜ[k] B)).map ψ =
        matrixAlgebraExtension n (ψ a ⊗ₜ[k] B) := by
      ext i j : 1
      simp only [matrixAlgebraExtension_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        map_mul, ψ.commutes]
    rw [hm, matrixLinearSystemExtension_tmul, matrixLinearSystemExtension_tmul]
    funext i
    rw [map_mul, ψ.commutes]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension.Construction
