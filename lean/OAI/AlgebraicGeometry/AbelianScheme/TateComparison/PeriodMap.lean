import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.Submodule.Map

/-! # Period Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodMap

noncomputable section

/-! An integral period gives its compatible q-power division points in
the actual period quotient. This construction is independent of a basis. -/

open scoped Pointwise

universe u
variable (q : ℕ) [Fact q.Prime]
  {V : Type u} [AddCommGroup V] [Module ℚ V] (L : Submodule ℤ V)

def periodDivisionPoint (n : ℕ) : L →+ (V ⧸ L.toAddSubgroup) :=
  (QuotientAddGroup.mk' L.toAddSubgroup).comp
    ((DistribSMul.toAddMonoidHom V ((q : ℚ) ^ n)⁻¹).comp L.subtype.toAddMonoidHom)

theorem periodDivisionPoint_killed (n : ℕ) (x : L) :
    q ^ n • periodDivisionPoint q L n x = 0 := by
  change q ^ n • (QuotientAddGroup.mk' L.toAddSubgroup) (((q : ℚ) ^ n)⁻¹ • x.val) = 0
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)), one_smul]
  exact (QuotientAddGroup.eq_zero_iff x.val).mpr x.property

theorem periodDivisionPoint_transition (n : ℕ) (x : L) :
    q • periodDivisionPoint q L (n + 1) x = periodDivisionPoint q L n x := by
  change q • (QuotientAddGroup.mk' L.toAddSubgroup) (((q : ℚ) ^ (n + 1))⁻¹ • x.val) =
    (QuotientAddGroup.mk' L.toAddSubgroup) (((q : ℚ) ^ n)⁻¹ • x.val)
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 2
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

/-- The compatible division sequence of a literal integral period. -/
def periodTateMap : L →ₗ[ℤ] Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q where
  toFun x := ⟨fun n => ⟨periodDivisionPoint q L n x, periodDivisionPoint_killed q L n x⟩,
    fun n => Subtype.ext (periodDivisionPoint_transition q L n x)⟩
  map_add' x y := Subtype.ext (funext fun n => Subtype.ext ((periodDivisionPoint q L n).map_add x y))
  map_smul' z x := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    exact (periodDivisionPoint q L n).map_zsmul z x

@[simp] theorem periodTateMap_evaluate (x : L) (n : ℕ) :
    ((periodTateMap q L x).val n).val =
      (QuotientAddGroup.mk' L.toAddSubgroup) (((q : ℚ) ^ n)⁻¹ • x.val) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodMap
