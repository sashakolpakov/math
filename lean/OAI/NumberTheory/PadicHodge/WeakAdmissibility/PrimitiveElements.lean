import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients

/-! # Primitive Elements -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements

noncomputable section

/-! A residue criterion for primitive generators of Fontaine's theta kernel. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel
variable (p : ℕ) [Fact p.Prime]

abbrev ResidueCp := IsLocalRing.ResidueField 𝓞_ℂ_[p]

theorem residueCp_p_zero : (p : ResidueCp p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue 𝓞_ℂ_[p]), IsLocalRing.residue_eq_zero_iff]
  exact Logarithm.PeriodRings.not_isUnit_p p

instance residueCp_charP : CharP (ResidueCp p) p :=
  (CharP.charP_iff_prime_eq_zero (R := ResidueCp p) (Fact.out : p.Prime)).mpr (residueCp_p_zero p)

def residueModP : ModP 𝓞_ℂ_[p] p →+* ResidueCp p :=
  Ideal.Quotient.lift _ (IsLocalRing.residue 𝓞_ℂ_[p]) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, map_natCast, residueCp_p_zero, zero_mul])

def tiltResidue : PreTilt 𝓞_ℂ_[p] p →+* ResidueCp p :=
  (residueModP p).comp (Perfection.coeff (ModP 𝓞_ℂ_[p] p) p 0)

theorem tiltResidue_untilt (a : PreTilt 𝓞_ℂ_[p] p) :
    tiltResidue p a = IsLocalRing.residue 𝓞_ℂ_[p] a.untilt := by
  have he := congrArg (residueModP p) (PreTilt.mk_untilt_eq_coeff_zero a)
  exact he.symm

theorem tilt_isUnit_of_residue_ne_zero (a : PreTilt 𝓞_ℂ_[p] p) (ha : tiltResidue p a ≠ 0) :
    IsUnit a := by
  have hu : IsUnit a.untilt := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    ((tiltResidue_untilt p a) ▸ ha)
  obtain ⟨u, hu⟩ := hu
  have hm : ‖(a.untilt : ℂ_[p])‖ * ‖((↑u⁻¹ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul]
    have he : (a.untilt : ℂ_[p]) * ((↑u⁻¹ : 𝓞_ℂ_[p]) : ℂ_[p]) = 1 := by
      have he := congrArg (fun b : 𝓞_ℂ_[p] => (b : ℂ_[p])) u.val_inv
      change ((↑u : 𝓞_ℂ_[p]) : ℂ_[p]) * ((↑u⁻¹ : 𝓞_ℂ_[p]) : ℂ_[p]) = 1 at he
      rwa [hu] at he
    rw [he, norm_one]
  have hn : 1 ≤ ‖(a.untilt : ℂ_[p])‖ := by
    rw [← hm]
    exact mul_le_of_le_one_right (norm_nonneg _) (Logarithm.PeriodRings.integer_norm_le_one p (↑u⁻¹))
  apply isUnit_of_dvd_one
  apply ThetaKernel.tilt_dvd_of_untilt_norm_le p 1 a
  · exact hu ▸ u.isUnit.ne_zero
  · simpa only [map_one, OneMemClass.coe_one, norm_one] using hn

theorem aInf_isUnit_of_coeff_zero (a : Logarithm.PeriodRings.AInf p) (ha : IsUnit (a.coeff 0)) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  let b : Logarithm.PeriodRings.AInf p := WittVector.teichmuller p (↑u⁻¹)
  have hm : a * b - 1 ∈ Ideal.span {(p : Logarithm.PeriodRings.AInf p)} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change WittVector.constantCoeff (a * b - 1) = 0
    rw [map_sub, map_mul, map_one]
    change a.coeff 0 * (WittVector.teichmuller p (↑u⁻¹)).coeff 0 - 1 = 0
    rw [WittVector.teichmuller_coeff_zero, ← hu]
    simp
  exact isUnit_of_mul_isUnit_left
    (Ideal.isUnit_of_sub_one_mem_jacobson_bot _
      (IsAdicComplete.le_jacobson_bot (I := Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) hm))

def wittResidue : Logarithm.PeriodRings.AInf p →+* WittVector p (ResidueCp p) := WittVector.map (tiltResidue p)

theorem wittResidue_thetaGenerator : wittResidue p (ThetaKernel.thetaGenerator p) = -(p : WittVector p (ResidueCp p)) := by
  change wittResidue p (WittVector.teichmuller p (ThetaKernel.pFlat p) - p) = _
  rw [map_sub, map_natCast]
  change WittVector.map (tiltResidue p) (WittVector.teichmuller p (ThetaKernel.pFlat p)) - p = _
  rw [WittVector.map_teichmuller, tiltResidue_untilt, ThetaKernel.pFlat_untilt,
    map_natCast, residueCp_p_zero, WittVector.teichmuller_zero, zero_sub]

/-- A theta-kernel element reducing to p in Witt vectors of the residue field is primitive. -/
theorem theta_generator_of_residue_p (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0)
    (hres : wittResidue p x = (p : WittVector p (ResidueCp p))) :
    RingHom.ker (Logarithm.PeriodRings.theta p) = Ideal.span {x} := by
  have hmem : x ∈ Ideal.span {ThetaKernel.thetaGenerator p} := ThetaKernel.theta_kernel_eq_span p ▸ RingHom.mem_ker.mpr hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  have he : wittResidue p b = -1 := by
    apply mul_left_cancel₀ (WittVector.p_nonzero p (ResidueCp p))
    rw [hb, map_mul, wittResidue_thetaGenerator] at hres
    calc
      (p : WittVector p (ResidueCp p)) * wittResidue p b = -(-(p : WittVector p (ResidueCp p)) * wittResidue p b) := by ring
      _ = -(p : WittVector p (ResidueCp p)) := congrArg Neg.neg hres
      _ = (p : WittVector p (ResidueCp p)) * -1 := by ring
  have hb₀ : tiltResidue p (b.coeff 0) = -1 := by
    have he₀ := congrArg (WittVector.constantCoeff : WittVector p (ResidueCp p) →+* ResidueCp p) he
    simpa only [wittResidue, WittVector.map_coeff, WittVector.constantCoeff_apply, map_neg, map_one] using he₀
  have hu := aInf_isUnit_of_coeff_zero p b
    (tilt_isUnit_of_residue_ne_zero p _ (hb₀ ▸ neg_ne_zero.mpr one_ne_zero))
  rw [ThetaKernel.theta_kernel_eq_span]
  apply Ideal.span_singleton_eq_span_singleton.mpr
  exact ⟨hu.unit, by rw [hu.unit_spec, ← hb]⟩

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements
