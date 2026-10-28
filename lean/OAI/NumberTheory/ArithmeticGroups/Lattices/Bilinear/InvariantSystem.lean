import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension

/-! # Invariant System -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantSystem.Construction

noncomputable section

/-! Finite linear equations for infinitesimally invariant bilinear
forms, and compatibility with extension of the coefficient field. -/

open scoped Classical TensorProduct
open _root_.Matrix

def bilinearLieVariation {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun Q := A.transpose * Q + Q * A
  map_add' Q R := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c Q := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

def bilinearInvariantSystem {k ι : Type} [Field k] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) k →ₗ[k] (ι × Fin n × Fin n → k) where
  toFun Q t := bilinearLieVariation (A t.1) Q t.2.1 t.2.2
  map_add' Q R := by ext t; exact congrArg (fun M => M t.2.1 t.2.2) (map_add (bilinearLieVariation (A t.1)) Q R)
  map_smul' c Q := by ext t; exact congrArg (fun M => M t.2.1 t.2.2) (map_smul (bilinearLieVariation (A t.1)) c Q)

theorem bilinearLieVariation_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (v : k →+* K)
    (A Q : Matrix (Fin n) (Fin n) k) :
    bilinearLieVariation (A.map v) (Q.map v) = (bilinearLieVariation A Q).map v := by
  change v.mapMatrix A.transpose * v.mapMatrix Q + v.mapMatrix Q * v.mapMatrix A =
    v.mapMatrix (A.transpose * Q + Q * A)
  rw [map_add, map_mul, map_mul]

theorem bilinearInvariantSystem_baseChange
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [Fintype ι] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) k) (x : K ⊗[k] Matrix (Fin n) (Fin n) k) :
    TensorProduct.piScalarRight k K K (ι × Fin n × Fin n)
        ((bilinearInvariantSystem A).baseChange K x) =
      bilinearInvariantSystem (fun i => (A i).map (algebraMap k K)) (MatrixFlatExtension.Construction.matrixScalarExtension n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a Q =>
      rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, MatrixFlatExtension.Construction.matrixScalarExtension_tmul, map_smul]
      funext t
      change bilinearLieVariation (A t.1) Q t.2.1 t.2.2 • a =
        a • bilinearLieVariation ((A t.1).map (algebraMap k K))
          (Q.map (algebraMap k K)) t.2.1 t.2.2
      rw [bilinearLieVariation_coefficient_map]
      change _ = a * algebraMap k K _
      rw [Algebra.smul_def, mul_comm]

theorem bilinearInvariantSystem_kernel_baseChange
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [Fintype ι] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) k) :
    MatrixFlatExtension.Construction.matrixSubspaceExtension (K := K) (bilinearInvariantSystem A).ker =
      (bilinearInvariantSystem (fun i => (A i).map (algebraMap k K))).ker := by
  ext Q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MatrixFlatExtension.Construction.submodule_baseChange_ker] at hx
    change bilinearInvariantSystem _ (MatrixFlatExtension.Construction.matrixScalarExtension n x) = 0
    rw [← bilinearInvariantSystem_baseChange]
    exact map_eq_zero_iff _ (TensorProduct.piScalarRight k K K (ι × Fin n × Fin n)).injective |>.mpr hx
  · intro hQ
    refine ⟨(MatrixFlatExtension.Construction.matrixScalarExtension n).symm Q, ?_, (MatrixFlatExtension.Construction.matrixScalarExtension n).apply_symm_apply Q⟩
    rw [MatrixFlatExtension.Construction.submodule_baseChange_ker]
    change (bilinearInvariantSystem A).baseChange K ((MatrixFlatExtension.Construction.matrixScalarExtension n).symm Q) = 0
    apply (TensorProduct.piScalarRight k K K (ι × Fin n × Fin n)).injective
    rw [map_zero, bilinearInvariantSystem_baseChange, LinearEquiv.apply_symm_apply]
    exact hQ

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantSystem.Construction
