import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Padic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Padic Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PadicSubgroups.Construction

noncomputable section

/-!
Every additive subgroup of a module killed by q^h is automatically
stable under the q-adic integers. This removes a possible extra condition
when passing from finite subgroup choices to q-adic intermediate lattices.
-/

variable (q : ℕ) [Fact q.Prime] {V : Type*}
  [AddCommGroup V] [Module ℤ_[q] V]

theorem padic_smul_eq_residue_nsmul (h : ℕ)
    (hkilled : ∀ x : V, (q : ℤ_[q]) ^ h • x = 0) (r : ℤ_[q]) (x : V) :
    r • x = (PadicInt.toZModPow h r).val • x := by
  have hres : r - ((PadicInt.toZModPow h r).val : ℤ_[q]) ∈
      Ideal.span {(q : ℤ_[q]) ^ h} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hres
  have hz : (r - ((PadicInt.toZModPow h r).val : ℤ_[q])) • x = 0 := by
    rw [hc, mul_comm, mul_smul, hkilled, smul_zero]
  simpa only [sub_smul, Nat.cast_smul_eq_nsmul, sub_eq_zero] using hz

/-- Subgroups and q-adic submodules of a killed module are the same
choices, with unchanged elements and inclusions. -/
def padicSubgroupOrderIso (h : ℕ)
    (hkilled : ∀ x : V, (q : ℤ_[q]) ^ h • x = 0) :
    AddSubgroup V ≃o Submodule ℤ_[q] V where
  toFun H :=
    { H with
      smul_mem' := by
        intro r x hx
        rw [padic_smul_eq_residue_nsmul q h hkilled]
        exact H.nsmul_mem hx _ }
  invFun := Submodule.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem mem_padicSubgroupOrderIso (h : ℕ)
    (hkilled : ∀ x : V, (q : ℤ_[q]) ^ h • x = 0) (H : AddSubgroup V) (x : V) :
    x ∈ padicSubgroupOrderIso q h hkilled H ↔ x ∈ H := Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PadicSubgroups.Construction
