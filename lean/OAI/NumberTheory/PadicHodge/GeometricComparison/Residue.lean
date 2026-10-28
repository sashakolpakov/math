import OAI.NumberTheory.PadicHodge.GeometricComparison.WittFrobenius
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Residue -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Residue.PadicBase

noncomputable section

/-! Compatibility of the actual Witt embedding with the p-adic residue map. -/

variable (q : ℕ) [Fact q.Prime]

theorem ringHom_eq_toZMod (f : ℤ_[q] →+* ZMod q) : f = PadicInt.toZMod := by
  apply RingHom.ext
  intro x
  have hx := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  have he := congrArg f ha
  have hm : f (ZMod.cast (PadicInt.toZMod x) : ℤ_[q]) = PadicInt.toZMod x := by
    rw [ZMod.cast_eq_val, map_natCast, ZMod.natCast_zmod_val]
  simp only [map_sub, map_mul, map_natCast, ZMod.natCast_self, zero_mul, hm] at he
  exact sub_eq_zero.mp he

theorem residueField_residue :
    (PadicInt.residueField (p := q)).toRingHom.comp (IsLocalRing.residue ℤ_[q]) =
      PadicInt.toZMod :=
  ringHom_eq_toZMod q _

theorem wittEquiv_residue :
    (PadicInt.toZMod : ℤ_[q] →+* ZMod q).comp (WittVector.equiv q).toRingHom =
      WittVector.constantCoeff := by
  have h := ringHom_eq_toZMod q
    ((WittVector.constantCoeff : Crystalline.CoefficientAdapter.Witt q →+* ZMod q).comp
      (WittVector.equiv q).symm.toRingHom)
  apply RingHom.ext
  intro w
  have hw := DFunLike.congr_fun h ((WittVector.equiv q) w)
  change WittVector.constantCoeff ((WittVector.equiv q).symm ((WittVector.equiv q) w)) =
    PadicInt.toZMod ((WittVector.equiv q) w) at hw
  rw [RingEquiv.symm_apply_apply] at hw
  exact hw.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Residue.PadicBase
