import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar Inverse Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarInverseLimit.FiniteScalarInverseLimit

noncomputable section

/-!
# Finite free scalar extension of compatible module systems

This is an isomorphism over the extension ring, with the original
algebra action. Its coordinate formula is the base change of evaluation.
-/

open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ℕ → Type u) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n m, n ≤ m → M m →ₗ[R] M n)

def transition (n m : ℕ) (h : n ≤ m) : S ⊗[R] M m →ₗ[S] S ⊗[R] M n :=
  (t n m h).baseChange S

abbrev compatible := Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible S (fun n => S ⊗[R] M n) (transition R S M t)

theorem comm_transition (n m : ℕ) (h : n ≤ m) (x : M m ⊗[R] S) :
    transition R S M t n m h (TensorProduct.comm R (M m) S x) =
      TensorProduct.comm R (M n) S (TensorProduct.map (t n m h) LinearMap.id x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m s => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def rightCompatibleEquiv :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R (fun n => M n ⊗[R] S)
      (TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition R S M t) ≃ₗ[R] compatible R S M t where
  toFun x := ⟨fun n => TensorProduct.comm R (M n) S (x.val n), by
    intro n m h
    rw [comm_transition]
    exact congrArg (TensorProduct.comm R (M n) S) (x.property n m h)⟩
  invFun x := ⟨fun n => TensorProduct.comm R S (M n) (x.val n), by
    intro n m h
    apply (TensorProduct.comm R (M n) S).injective
    change TensorProduct.comm R (M n) S
      (TensorProduct.map (t n m h) LinearMap.id (TensorProduct.comm R S (M m) (x.val m))) =
        TensorProduct.comm R (M n) S (TensorProduct.comm R S (M n) (x.val n))
    rw [← comm_transition]
    exact (congrArg (transition R S M t n m h)
      ((TensorProduct.comm R S (M m)).symm_apply_apply (x.val m))).trans
        ((x.property n m h).trans
          ((TensorProduct.comm R S (M n)).symm_apply_apply (x.val n)).symm)⟩
  left_inv x := Subtype.ext (funext (fun n => (TensorProduct.comm R (M n) S).symm_apply_apply _))
  right_inv x := Subtype.ext (funext (fun n => (TensorProduct.comm R S (M n)).symm_apply_apply _))
  map_add' x y := Subtype.ext (funext (fun n => (TensorProduct.comm R (M n) S).map_add _ _))
  map_smul' r x := Subtype.ext (funext (fun n => (TensorProduct.comm R (M n) S).map_smul r _))

variable (ξ : Type u) [Fintype ξ] (b : Module.Basis ξ R S)

def equivR : S ⊗[R] Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t ≃ₗ[R] compatible R S M t :=
  (TensorProduct.comm R S (Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t)).trans
    ((TensorInverseLimit.FiniteTensorInverseLimit.equiv R ξ S b M t).trans (rightCompatibleEquiv R S M t))

theorem equivR_eval (n : ℕ) (z : S ⊗[R] Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t) :
    (equivR R S M t ξ b z).val n = (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R M t n).baseChange S z := by
  change TensorProduct.comm R (M n) S
    ((TensorInverseLimit.FiniteTensorInverseLimit.equiv R ξ S b M t
      (TensorProduct.comm R S (Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t) z)).val n) = _
  have he := congrArg (TensorProduct.comm R (M n) S)
    (TensorInverseLimit.FiniteTensorInverseLimit.equiv_eval R ξ S b M t n
      (TensorProduct.comm R S (Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t) z))
  refine he.trans ?_
  clear he
  induction z using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def map : S ⊗[R] Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t →ₗ[S] compatible R S M t where
  toFun := equivR R S M t ξ b
  map_add' := (equivR R S M t ξ b).map_add
  map_smul' s z := by
    apply Subtype.ext
    funext n
    change (equivR R S M t ξ b (s • z)).val n = s • (equivR R S M t ξ b z).val n
    rw [equivR_eval, equivR_eval]
    exact ((Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R M t n).baseChange S).map_smul s z

def equiv : S ⊗[R] Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t ≃ₗ[S] compatible R S M t :=
  LinearEquiv.ofBijective (FiniteScalarInverseLimit.map R S M t ξ b) (equivR R S M t ξ b).bijective

theorem equiv_eval (n : ℕ) (z : S ⊗[R] Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R M t) :
    (equiv R S M t ξ b z).val n = (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R M t n).baseChange S z :=
  equivR_eval R S M t ξ b n z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarInverseLimit.FiniteScalarInverseLimit
