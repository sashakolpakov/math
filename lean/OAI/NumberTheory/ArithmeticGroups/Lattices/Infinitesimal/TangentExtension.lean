import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TangentEquations
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension

/-! # Tangent Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension.Construction

noncomputable section

section

/-! A finite system of matrix tangent equations commutes with scalar
extension, including its kernel. -/

open scoped Classical TensorProduct

theorem tangentSystem_baseChange
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [Fintype ι] {n : ℕ}
    (p : ι → Algebraic.CoordinatePolynomial n k) (x : K ⊗[k] Matrix (Fin n) (Fin n) k) :
    TensorProduct.piScalarRight k K K ι ((Finite.TangentEquations.Construction.tangentSystem p).baseChange K x) =
      Finite.TangentEquations.Construction.tangentSystem (fun i => MvPolynomial.map (algebraMap k K) (p i)) (MatrixFlatExtension.Construction.matrixScalarExtension n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a A =>
      rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, MatrixFlatExtension.Construction.matrixScalarExtension_tmul, map_smul]
      funext i
      change Finite.TangentEquations.Construction.tangentFunctional (p i) A • a =
        a • Finite.TangentEquations.Construction.tangentFunctional (MvPolynomial.map (algebraMap k K) (p i)) (A.map (algebraMap k K))
      have hc : Finite.TangentEquations.Construction.tangentFunctional (MvPolynomial.map (algebraMap k K) (p i))
          (A.map (algebraMap k K)) = algebraMap k K (Finite.TangentEquations.Construction.tangentFunctional (p i) A) :=
        CoefficientMap.Construction.tangent_coefficient_map _ A (p i)
      rw [hc, Algebra.smul_def, smul_eq_mul, mul_comm]

theorem tangentSystem_kernel_baseChange
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [Fintype ι] {n : ℕ}
    (p : ι → Algebraic.CoordinatePolynomial n k) :
    MatrixFlatExtension.Construction.matrixSubspaceExtension (K := K) (Finite.TangentEquations.Construction.tangentSystem p).ker =
      (Finite.TangentEquations.Construction.tangentSystem (fun i => MvPolynomial.map (algebraMap k K) (p i))).ker := by
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MatrixFlatExtension.Construction.submodule_baseChange_ker] at hx
    change Finite.TangentEquations.Construction.tangentSystem _ (MatrixFlatExtension.Construction.matrixScalarExtension n x) = 0
    rw [← tangentSystem_baseChange]
    exact map_eq_zero_iff _ (TensorProduct.piScalarRight k K K ι).injective |>.mpr hx
  · intro hA
    refine ⟨(MatrixFlatExtension.Construction.matrixScalarExtension n).symm A, ?_, (MatrixFlatExtension.Construction.matrixScalarExtension n).apply_symm_apply A⟩
    rw [MatrixFlatExtension.Construction.submodule_baseChange_ker]
    change (Finite.TangentEquations.Construction.tangentSystem p).baseChange K ((MatrixFlatExtension.Construction.matrixScalarExtension n).symm A) = 0
    apply (TensorProduct.piScalarRight k K K ι).injective
    rw [map_zero, tangentSystem_baseChange, LinearEquiv.apply_symm_apply]
    exact hA

end

section

/-! The Lie algebra of a geometrically connected characteristic-zero
matrix group is obtained by scalar extension of its original Lie algebra. -/

open scoped Classical TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

theorem matrixGroupBaseChange_self
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    BaseChange.Construction.matrixGroupBaseChange G (algebraMap k k) = G := by
  cases G
  simp [BaseChange.Construction.matrixGroupBaseChange]
  convert Set.image_id _ using 1
  congr 1
  funext p
  exact MvPolynomial.map_id p

theorem infinitesimalStabilizer_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    MatrixFlatExtension.Construction.matrixSubspaceExtension (K := K) (Action.Construction.infinitesimalStabilizer G).toSubmodule =
      (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule := by
  obtain ⟨ι, hι, p, hp⟩ := Finite.TangentEquations.Construction.exists_uniform_finite_tangent_system G hG
  let : Fintype ι := hι
  have hk : (Action.Construction.infinitesimalStabilizer G).toSubmodule = (Finite.TangentEquations.Construction.tangentSystem p).ker := by
    have hh := hp k
    rw [matrixGroupBaseChange_self] at hh
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hh
  rw [hk, tangentSystem_kernel_baseChange, hp K]

theorem infinitesimalStabilizer_eq_span_base
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule =
      Submodule.span K ((fun A : Matrix (Fin n) (Fin n) k => A.map (algebraMap k K)) ''
        (Action.Construction.infinitesimalStabilizer G : Set (Matrix (Fin n) (Fin n) k))) := by
  rw [← infinitesimalStabilizer_baseChange G hG, MatrixFlatExtension.Construction.matrixSubspaceExtension_eq_span]
  rfl

end

/-! Commutation with the entire Lie algebra persists under scalar extension. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_commuting_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) k)
    (hC : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, A * C = C * A)
    {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) :
    A * C.map (algebraMap k K) = C.map (algebraMap k K) * A := by
  change A ∈ (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule at hA
  rw [infinitesimalStabilizer_eq_span_base G hG] at hA
  induction hA using Submodule.span_induction with
  | mem B hB =>
      obtain ⟨B, hB, rfl⟩ := hB
      simpa only [map_mul, RingHom.mapMatrix_apply] using
        congrArg (algebraMap k K).mapMatrix (hC B hB)
  | zero => rw [Matrix.zero_mul, Matrix.mul_zero]
  | add A B _ _ hA hB => rw [Matrix.add_mul, Matrix.mul_add, hA, hB]
  | smul a A _ hA => rw [Matrix.smul_mul, Matrix.mul_smul, hA]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension.Construction
