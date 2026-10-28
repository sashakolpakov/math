import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Tensor Contraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.TensorContraction.CM.SurfaceConstruction

noncomputable section

/-!
The linear contraction in SurfaceConstruction, on actual tensor products over the coefficient
field. This module proves its value and nonvanishing; identifying the operation
with a geometric cup/pushforward correspondence is a separate geometric step.
-/

open scoped TensorProduct

variable (E : Type*) [Field E]
variable (V W : Fin 4 → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module E (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module E (W i)]

abbrev FourTensor := (V 0 ⊗[E] V 1) ⊗[E] (V 2 ⊗[E] V 3)

def fourTensor (v : ∀ i, V i) : FourTensor E V :=
  (v 0 ⊗ₜ[E] v 1) ⊗ₜ[E] (v 2 ⊗ₜ[E] v 3)

/-- Regroup the four original/copy pairs into original and copy variables. -/
def regroupPairs :
    FourTensor E (fun i => V i ⊗[E] W i) ≃ₗ[E]
      FourTensor E V ⊗[E] FourTensor E W :=
  (TensorProduct.congr
    (TensorProduct.tensorTensorTensorComm E (V 0) (W 0) (V 1) (W 1))
    (TensorProduct.tensorTensorTensorComm E (V 2) (W 2) (V 3) (W 3))).trans
    (TensorProduct.tensorTensorTensorComm E
      (V 0 ⊗[E] V 1) (W 0 ⊗[E] W 1)
      (V 2 ⊗[E] V 3) (W 2 ⊗[E] W 3))

@[simp]
theorem regroupPairs_fourTensor (v : ∀ i, V i) (w : ∀ i, W i) :
    regroupPairs E V W (fourTensor E _ (fun i => v i ⊗ₜ[E] w i)) =
      fourTensor E V v ⊗ₜ[E] fourTensor E W w := rfl

/-- Contract only the original variables against their linear functional. -/
def contractPairs (ell : FourTensor E V →ₗ[E] E) :
    FourTensor E (fun i => V i ⊗[E] W i) →ₗ[E] FourTensor E W :=
  (TensorProduct.lid E (FourTensor E W)).toLinearMap.comp
    ((TensorProduct.map ell LinearMap.id).comp (regroupPairs E V W).toLinearMap)

/-- The coefficient is exactly the functional on the original tensor. -/
theorem contractPairs_fourTensor (ell : FourTensor E V →ₗ[E] E)
    (v : ∀ i, V i) (w : ∀ i, W i) :
    contractPairs E V W ell (fourTensor E _ (fun i => v i ⊗ₜ[E] w i)) =
      ell (fourTensor E V v) • fourTensor E W w := rfl

theorem simpleTensor_ne_zero {M N : Type*}
    [AddCommGroup M] [Module E M] [AddCommGroup N] [Module E N]
    {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) : m ⊗ₜ[E] n ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis E M
  have hr : b.repr m ≠ 0 := by
    intro h
    exact hm (b.repr.injective (h.trans b.repr.map_zero.symm))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hr
  intro h
  have he := congrArg (fun t => TensorProduct.equivFinsuppOfBasisLeft b t i) h
  simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
    map_zero, Finsupp.zero_apply] at he
  exact (smul_ne_zero hi hn) he

theorem fourTensor_ne_zero (v : ∀ i, V i) (hv : ∀ i, v i ≠ 0) :
    fourTensor E V v ≠ 0 :=
  simpleTensor_ne_zero E
    (simpleTensor_ne_zero E (hv 0) (hv 1))
    (simpleTensor_ne_zero E (hv 2) (hv 3))

/-- A nonzero surface functional produces a nonzero generator on the copies. -/
theorem contractPairs_ne_zero (ell : FourTensor E V →ₗ[E] E)
    (v : ∀ i, V i) (w : ∀ i, W i)
    (hell : ell (fourTensor E V v) ≠ 0) (hw : ∀ i, w i ≠ 0) :
    contractPairs E V W ell (fourTensor E _ (fun i => v i ⊗ₜ[E] w i)) ≠ 0 := by
  rw [contractPairs_fourTensor]
  exact smul_ne_zero hell (fourTensor_ne_zero E W w hw)

/-- The contracted class spans exactly the prescribed line on the copies. -/
theorem contractPairs_span (ell : FourTensor E V →ₗ[E] E)
    (v : ∀ i, V i) (w : ∀ i, W i)
    (hell : ell (fourTensor E V v) ≠ 0) :
    Submodule.span E
      {contractPairs E V W ell (fourTensor E _ (fun i => v i ⊗ₜ[E] w i))} =
      Submodule.span E {fourTensor E W w} := by
  rw [contractPairs_fourTensor]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hell) _

/-- Six exchanges of odd degree-one factors introduce total sign +1
when the four pair classes are regrouped into original and copy variables. -/
theorem fourPair_regrouping_sign : (-1 : E) ^ 6 = 1 := by
  norm_num

end

end OAI.AlgebraicGeometry.HodgeConjecture.TensorContraction.CM.SurfaceConstruction
