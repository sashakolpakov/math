import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import Mathlib.RingTheory.Ideal.Maps

/-! # Tensor Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReduction

noncomputable section

/-! The reduction of the actual dual-number tensor product is surjective,
and its kernel is exactly the extended square-zero ideal of the base. -/

open scoped TensorProduct

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

def dualScalarReductionIdeal : Ideal (DualNumber k) :=
  RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom

theorem dualScalarReductionIdeal_square : dualScalarReductionIdeal k * dualScalarReductionIdeal k = ⊥ := by
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    change x * y = 0
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    apply TrivSqZeroExt.ext
    · change x.fst * y.fst = 0
      rw [hx, zero_mul]
    · rw [DualNumber.snd_mul, hx, hy, zero_mul, mul_zero, add_zero]
      rfl
  · exact bot_le

def dualTensorReduction : (DualNumber k ⊗[k] A) →ₐ[k] A :=
  (TrivSqZeroExt.fstHom k A A).comp (NumberCoefficients.dualTensorCoefficients k A)

theorem dualTensorReduction_tmul (c : DualNumber k) (a : A) :
    dualTensorReduction k A (c ⊗ₜ[k] a) = c.fst • a := by
  change (NumberCoefficients.dualTensorCoefficients k A (c ⊗ₜ[k] a)).fst = _
  rw [NumberCoefficients.dualTensorCoefficients_tmul]
  rfl

theorem dualTensorReduction_surjective : Function.Surjective (dualTensorReduction k A) := by
  intro a
  refine ⟨(1 : DualNumber k) ⊗ₜ[k] a, ?_⟩
  rw [dualTensorReduction_tmul]
  exact one_smul k a

def dualTensorReductionIdeal : Ideal (DualNumber k ⊗[k] A) :=
  (dualScalarReductionIdeal k).map
    (Algebra.TensorProduct.includeLeft : DualNumber k →ₐ[k] DualNumber k ⊗[k] A).toRingHom

theorem dualTensorReduction_ker :
    RingHom.ker (dualTensorReduction k A) = dualTensorReductionIdeal k A := by
  apply le_antisymm
  · intro u hu
    change (NumberCoefficients.dualTensorCoefficients k A u).fst = 0 at hu
    have hrepr := NumberCoefficients.dualTensorCoefficients_leftInverse (k := k) (R := A) u
    rw [NumberCoefficients.dualTensorFromCoefficients_apply, hu, TensorProduct.tmul_zero, zero_add] at hrepr
    rw [← hrepr]
    have heps : (DualNumber.eps : DualNumber k) ∈ dualScalarReductionIdeal k := by
      change (DualNumber.eps : DualNumber k).fst = 0
      rfl
    have hm := (dualTensorReductionIdeal k A).mul_mem_left
      ((1 : DualNumber k) ⊗ₜ[k] (NumberCoefficients.dualTensorCoefficients k A u).snd)
      (Ideal.mem_map_of_mem
        (Algebra.TensorProduct.includeLeft : DualNumber k →ₐ[k] DualNumber k ⊗[k] A).toRingHom heps)
    change ((1 : DualNumber k) ⊗ₜ[k] (NumberCoefficients.dualTensorCoefficients k A u).snd) *
      ((DualNumber.eps : DualNumber k) ⊗ₜ[k] (1 : A)) ∈ _ at hm
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] using hm
  · unfold dualTensorReductionIdeal
    apply (Ideal.map_le_iff_le_comap).mpr
    intro c hc
    change dualTensorReduction k A (c ⊗ₜ[k] (1 : A)) = 0
    change c.fst = 0 at hc
    rw [dualTensorReduction_tmul, hc, zero_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReduction
