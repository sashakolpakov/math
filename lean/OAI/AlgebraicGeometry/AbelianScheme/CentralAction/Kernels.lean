import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Scalar

/-! # Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Kernels.Construction

noncomputable section

/-! Scheme-theoretic scalar kernels on the actual chosen split blocks.
The q-adic unit factor does not change the kernel; this is proved for
every test scheme, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups

theorem torsion_coprime_power_eq_one_iff {G : Type*} [Group G]
    (x : G) (N k : ℕ) (hx : x ^ N = 1) (hk : Nat.Coprime k N) :
    x ^ k = 1 ↔ x = 1 := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
      (hk.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx))
    rw [h, one_pow] at hm
    exact hm.symm
  · rintro rfl
    exact one_pow _

theorem torsion_unit_residue_kernel {G : Type*} [Group G]
    (x : G) (N : ℕ) [NeZero N] (hx : x ^ N = 1)
    (a : ℕ) (u : (ZMod N)ˣ) :
    x ^ (((a : ZMod N) * u).val) = 1 ↔ x ^ a = 1 := by
  have hmod : (((a : ZMod N) * u).val) ≡ a * (u : ZMod N).val [MOD N] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp
  rw [pow_eq_pow_of_modEq hmod hx, pow_mul]
  have hy : (x ^ a) ^ N = 1 := by rw [pow_right_comm, hx, one_pow]
  have hu : Nat.Coprime (u : ZMod N).val N := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simp
  exact torsion_coprime_power_eq_one_iff (x ^ a) N _ hy hu

universe u
variable {E : Type u} [Field E] {g N q : ℕ} [Fact q.Prime] {S : Scheme.{u}}

/-- On a chosen q^h-block, a scalar with local value q^a times a unit
has precisely the q^a-torsion kernel. -/
theorem scalar_kernel_on_splitBlock
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (χ : NumberField.RingOfIntegers E →+* ℤ_[q])
    (b : NumberField.RingOfIntegers E) (h a : ℕ) (u : ℤ_[q]ˣ)
    (hlocal : χ b = (q : ℤ_[q]) ^ a * u)
    (T : Over S) (x : T ⟶ D.abelian.scheme)
    (hblock : x ∈ (TateComparison.Subgroups.splitBlock D χ h).atTest T) :
    x ≫ Scalar.Construction.scalarMap D b = 1 ↔ x ^ (q ^ a) = 1 := by
  have hx : x ^ (q ^ h) = 1 := hblock.1
  have haction : x ≫ Scalar.Construction.scalarMap D b = x ^ (PadicInt.toZModPow h (χ b)).val := hblock.2 b
  let ur : (ZMod (q ^ h))ˣ := Units.map (PadicInt.toZModPow h).toMonoidHom u
  rw [haction, hlocal, map_mul, map_pow, map_natCast]
  have he : (q : ZMod (q ^ h)) ^ a * PadicInt.toZModPow h (u : ℤ_[q]) =
      ((q ^ a : ℕ) : ZMod (q ^ h)) * (ur : ZMod (q ^ h)) := by
    rw [Nat.cast_pow]
    rfl
  rw [he]
  exact torsion_unit_residue_kernel x (q ^ h) hx (q ^ a) ur

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Kernels.Construction
