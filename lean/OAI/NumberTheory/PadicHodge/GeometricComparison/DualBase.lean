import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.Tactic

/-! # Dual Base -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DualBase.DualBaseChange

noncomputable section

/-! The native dual tensor equivalence and its naturality under precomposition. -/

open scoped TensorProduct

variable {R S V W : Type*} [Field R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [FiniteDimensional R V]
  [AddCommGroup W] [Module R W] [FiniteDimensional R W]

def equiv (S : Type*) [Field S] [Algebra R S] (V : Type*) [AddCommGroup V]
    [Module R V] [FiniteDimensional R V] :
    (S ⊗[R] Module.Dual R V) ≃ₗ[S] Module.Dual S (S ⊗[R] V) :=
  (TensorProduct.isBaseChange (R := R) (M := V) (S := S)).toDualBaseChange

theorem equiv_tmul_one (a : S) (f : Module.Dual R V) (v : V) :
    equiv S V (a ⊗ₜ[R] f) (1 ⊗ₜ[R] v) = a * algebraMap R S (f v) :=
  IsBaseChange.toDualBaseChange_tmul (TensorProduct.isBaseChange (R := R) (M := V) (S := S)) a f v

theorem equiv_tmul_tmul (a b : S) (f : Module.Dual R V) (v : V) :
    equiv S V (a ⊗ₜ[R] f) (b ⊗ₜ[R] v) = b * (a * algebraMap R S (f v)) := by
  have hb : b ⊗ₜ[R] v = b • ((1 : S) ⊗ₜ[R] v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hb, map_smul, equiv_tmul_one, smul_eq_mul]

theorem naturality (f : V →ₗ[R] W) (x : S ⊗[R] Module.Dual R W) :
    equiv S V (f.dualMap.baseChange S x) = (equiv S W x).comp (f.baseChange S) := by
  induction x using TensorProduct.inductionOn with
  | tmul a g =>
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul b v =>
          change equiv S V (a ⊗ₜ[R] (g.comp f)) (b ⊗ₜ[R] v) =
            equiv S W (a ⊗ₜ[R] g) (b ⊗ₜ[R] f v)
          rw [equiv_tmul_tmul, equiv_tmul_tmul, LinearMap.comp_apply]
      | add y z hy hz => simp only [map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DualBase.DualBaseChange
