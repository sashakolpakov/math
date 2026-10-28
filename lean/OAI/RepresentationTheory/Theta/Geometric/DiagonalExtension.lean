import OAI.RepresentationTheory.Theta.Geometric.DiagonalEigen
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Diagonal Extension -/

namespace OAI.RepresentationTheory.Theta.Geometric.DiagonalExtension

noncomputable section

/-! A proved diagonal action retains its diagonal coordinates after
extension of the scalar field. -/

open scoped TensorProduct Classical

variable {R k I : Type} [Ring R] [Field k] [Fintype I] [DecidableEq I]
  (χ : I → R →+* k)

def diagonalOperator (a : R) : Module.End k (I → k) :=
  LinearMap.pi (fun i => χ i a • LinearMap.proj i)

variable (F : Type) [Field F] [Algebra k F]

theorem tensorDiagonal_coordinates (a : R) (z : F ⊗[k] (I → k)) :
    TensorProduct.piScalarRight k F F I ((diagonalOperator χ a).baseChange F z) =
      diagonalOperator (fun i => (algebraMap k F).comp (χ i)) a
        (TensorProduct.piScalarRight k F F I z) := by
  induction z using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c v =>
      funext i
      simp only [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      change (χ i a * v i) • c = algebraMap k F (χ i a) * (v i • c)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

variable {V : Type} [AddCommGroup V] [Module k V]
  (e : (I → k) ≃ₗ[k] V) (A : R → Module.End k V)
  (hA : ∀ a v, A a (e v) = e (diagonalOperator χ a v))

def extendedDiagonalEquiv : (I → F) ≃ₗ[F] F ⊗[k] V :=
  (TensorProduct.piScalarRight k F F I).symm.trans (e.baseChange k F _ _)

include hA

omit [Fintype I] [DecidableEq I] in
theorem tensorAction_intertwining (a : R) (z : F ⊗[k] (I → k)) :
    (A a).baseChange F ((e.baseChange k F _ _) z) =
      (e.baseChange k F _ _) ((diagonalOperator χ a).baseChange F z) := by
  induction z using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c v => exact congrArg (fun w : V => c ⊗ₜ[k] w) (hA a v)

theorem extendedDiagonal_intertwining (a : R) (v : I → F) :
    (A a).baseChange F (extendedDiagonalEquiv F e v) =
      extendedDiagonalEquiv F e (diagonalOperator (fun i => (algebraMap k F).comp (χ i)) a v) := by
  change (A a).baseChange F ((e.baseChange k F _ _) ((TensorProduct.piScalarRight k F F I).symm v)) = _
  rw [tensorAction_intertwining χ F e A hA]
  apply (e.baseChange k F _ _).congr_arg
  apply (TensorProduct.piScalarRight k F F I).injective
  rw [tensorDiagonal_coordinates, LinearEquiv.apply_symm_apply]
  exact ((TensorProduct.piScalarRight k F F I).apply_symm_apply _).symm

omit e A hA [DecidableEq I] in
theorem extendedDiagonal_finrank (τ : R →+* k) :
    Module.finrank F (DiagonalEigen.diagonalEigenSpace (fun i => (algebraMap k F).comp (χ i))
      ((algebraMap k F).comp τ)) = Fintype.card {i : I // χ i = τ} := by
  rw [DiagonalEigen.diagonalEigen_finrank]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => ⟨fun h => RingHom.ext (fun a =>
    (algebraMap k F).injective (congrArg (fun f : R →+* F => f a) h)), fun h => congrArg _ h⟩)

end

end OAI.RepresentationTheory.Theta.Geometric.DiagonalExtension
