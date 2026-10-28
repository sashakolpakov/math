import OAI.NumberTheory.Quaternion.Arithmetic.AdjointAssociativeDensity
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Tensor Invariant Subspaces -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TensorInvariantSubspaces

noncomputable section

/-! A subspace after field extension that is invariant under every
extended base-field endomorphism is zero or the whole space. Rank-one
operators extract each basis coordinate. -/

open scoped Classical TensorProduct
open _root_.Module

variable {k K V : Type*} [Field k] [Field K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

theorem baseChange_rankOne_apply
    {ι : Type*} (b : Basis ι k V) (i j : ι) (x : K ⊗[k] V) :
    ((b.coord i).smulRight (b j)).baseChange K x =
      (b.baseChange K).repr x i • (b.baseChange K) j := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, add_smul, hx, hy]
  | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearMap.smulRight_apply, Basis.coord_apply,
        Basis.baseChange_repr_tmul, Basis.baseChange_apply]
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem tensor_invariant_subspace_eq_bot_or_top [FiniteDimensional k V]
    (W : Submodule K (K ⊗[k] V))
    (hW : ∀ f : Module.End k V, ∀ x ∈ W, f.baseChange K x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  right
  let b := Module.finBasis k V
  let bK := b.baseChange K
  obtain ⟨x, hx, hx0⟩ := W.ne_bot_iff.mp h0
  obtain ⟨i, hi⟩ : ∃ i, bK.repr x i ≠ 0 := by
    by_contra! h
    apply hx0
    apply bK.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i
  have hb (j) : bK j ∈ W := by
    have hm := hW ((b.coord i).smulRight (b j)) x hx
    rw [baseChange_rankOne_apply] at hm
    change bK.repr x i • bK j ∈ W at hm
    have hh := W.smul_mem (bK.repr x i)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using hh
  apply top_unique
  intro y _
  rw [← bK.sum_repr y]
  exact W.sum_mem (fun j _ => W.smul_mem _ (hb j))

end

end OAI.NumberTheory.Quaternion.Arithmetic.TensorInvariantSubspaces
