import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateTorsion
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tate Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateInjection.Construction

noncomputable section

/-! The actual Tate module is torsion free. Rationalization is injective,
and divisibility in its integral image detects finite-level vanishing. -/

open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime] {H : Type*} [AddCommGroup H]

theorem tate_q_pow_smul_injective (n : ℕ) :
    Function.Injective (fun x : TateComparison.Add.Tate.Module (H := H) q => (q : ℤ_[q]) ^ n • x) := by
  intro x y hxy
  change (q : ℤ_[q]) ^ n • x = (q : ℤ_[q]) ^ n • y at hxy
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at hxy
  apply Subtype.ext
  funext k
  apply Subtype.ext
  have he := congrArg (fun z : TateComparison.Add.Tate.Module (H := H) q => (z.val (k + n)).val) hxy
  change q ^ n • (x.val (k + n)).val = q ^ n • (y.val (k + n)).val at he
  rw [TateTorsion.Construction.tate_transition_iterate, TateTorsion.Construction.tate_transition_iterate] at he
  exact he

instance tate_isTorsionFree : Module.IsTorsionFree ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q) where
  isSMulRegular r hr x y hxy := by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      hr.ne_zero (PadicInt.irreducible_p (p := q))
    change r • x = r • y at hxy
    rw [hu, mul_smul, mul_smul] at hxy
    have he := congrArg (fun z : TateComparison.Add.Tate.Module (H := H) q => (u⁻¹ : ℤ_[q]ˣ) • z) hxy
    simp only [Units.smul_def, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at he
    exact tate_q_pow_smul_injective q n he

def tateIntegralMap : TateComparison.Add.Tate.Module (H := H) q →ₗ[ℤ_[q]]
    ℚ_[q] ⊗[ℤ_[q]] TateComparison.Add.Tate.Module (H := H) q := TensorProduct.mk ℤ_[q] ℚ_[q] _ 1

theorem tateIntegralMap_injective : Function.Injective (tateIntegralMap (H := H) q) :=
  Module.Flat.tensorProduct_mk_injective (R := ℤ_[q]) (S := ℚ_[q]) (M := TateComparison.Add.Tate.Module (H := H) q)

theorem tateIntegralMap_qpow_smul (n : ℕ) (x : TateComparison.Add.Tate.Module (H := H) q) :
    tateIntegralMap q ((q : ℤ_[q]) ^ n • x) =
      (q : ℚ_[q]) ^ n • tateIntegralMap q x := by
  rw [map_smul]
  have he : algebraMap ℤ_[q] ℚ_[q] ((q : ℤ_[q]) ^ n) = (q : ℚ_[q]) ^ n := by simp
  rw [← he, IsScalarTower.algebraMap_smul]

/-- Vanishing at level n is exactly divisibility by q^n within the
integral image in the rational Tate space. -/
theorem tateEvaluation_zero_iff_rational_divisible (n : ℕ) (x : TateComparison.Add.Tate.Module (H := H) q) :
    TateTorsion.Construction.tateEvaluation q n x = 0 ↔ ∃ y : TateComparison.Add.Tate.Module (H := H) q,
      tateIntegralMap q x = (q : ℚ_[q]) ^ n • tateIntegralMap q y := by
  rw [TateTorsion.Construction.tateEvaluation_kernel]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, tateIntegralMap_qpow_smul q n y⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, tateIntegralMap_injective q ?_⟩
    rw [tateIntegralMap_qpow_smul, ← hy]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateInjection.Construction
