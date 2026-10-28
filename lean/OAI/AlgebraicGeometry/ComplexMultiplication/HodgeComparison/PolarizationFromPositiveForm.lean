import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalBilinearConjugation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Polarization From Positive Form -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm.CM.Construction

noncomputable section

/-! A positive rational alternating form isotropic on the holomorphic
part is a polarization of an arbitrary weight-one Hodge structure. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem weightOne_fixed_decomposition (H : WeightOne.CM.WeightOneHodgeStructure U)
    (x : WeightOne.CM.Complexification U) (hx : WeightOne.CM.coefficientConjugation U x = x) :
    ∃ p ∈ H.holomorphic, p + WeightOne.CM.coefficientConjugation U p = x := by
  have hm : x ∈ H.holomorphic ⊔ H.antiholomorphic := by
    rw [H.complementary.sup_eq_top]
    trivial
  obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hm
  have hc := congrArg (WeightOne.CM.coefficientConjugation U) he
  rw [map_add, hx] at hc
  have hcp : WeightOne.CM.coefficientConjugation U p ∈ H.antiholomorphic := (H.conjugate_mem p).mpr hp
  have hcq : WeightOne.CM.coefficientConjugation U q ∈ H.holomorphic :=
    (H.conjugate_mem _).mp (by simpa using hq)
  have hd : q - WeightOne.CM.coefficientConjugation U p = WeightOne.CM.coefficientConjugation U q - p := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using he.trans hc.symm
  have hzero : q - WeightOne.CM.coefficientConjugation U p = 0 := by
    apply (Submodule.disjoint_def.mp H.complementary.disjoint)
    · rw [hd]
      exact H.holomorphic.sub_mem hcq hp
    · exact H.antiholomorphic.sub_mem hq hcp
  exact ⟨p, hp, by rwa [← sub_eq_zero.mp hzero]⟩

theorem rationalBilinear_antiholomorphic_isotropic (H : WeightOne.CM.WeightOneHodgeStructure U)
    (B : LinearMap.BilinForm ℚ U)
    (hiso : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, B.baseChange ℂ u v = 0)
    (u : WeightOne.CM.Complexification U) (hu : u ∈ H.antiholomorphic)
    (v : WeightOne.CM.Complexification U) (hv : v ∈ H.antiholomorphic) : B.baseChange ℂ u v = 0 := by
  have hcu : WeightOne.CM.coefficientConjugation U u ∈ H.holomorphic :=
    (H.conjugate_mem _).mp (by simpa using hu)
  have hcv : WeightOne.CM.coefficientConjugation U v ∈ H.holomorphic :=
    (H.conjugate_mem _).mp (by simpa using hv)
  have h := RationalBilinearConjugation.CM.Construction.rationalBilinear_baseChange_conjugate B
    (WeightOne.CM.coefficientConjugation U u) (WeightOne.CM.coefficientConjugation U v)
  rw [hiso _ hcu _ hcv, star_zero, WeightOne.CM.coefficientConjugation_involutive,
    WeightOne.CM.coefficientConjugation_involutive] at h
  exact h.symm

theorem positiveAlternating_nondegenerate (H : WeightOne.CM.WeightOneHodgeStructure U)
    (B : LinearMap.BilinForm ℚ U) (hB : B.IsAlt)
    (hiso : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, B.baseChange ℂ u v = 0)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * B.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re) : B.Nondegenerate := by
  apply (hB.isRefl.nondegenerate_iff_separatingLeft).mpr
  intro x hx
  have hcx (v : WeightOne.CM.Complexification U) : B.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℚ] x) v = 0 := by
    induction v using TensorProduct.inductionOn with
    | tmul z y => simp [hx y]
    | add v w hv hw => simp [hv, hw]
  obtain ⟨p, hp, he⟩ := weightOne_fixed_decomposition H ((1 : ℂ) ⊗ₜ[ℚ] x) (by simp)
  have hcp : WeightOne.CM.coefficientConjugation U p ∈ H.antiholomorphic := (H.conjugate_mem p).mpr hp
  have hz := hcx (WeightOne.CM.coefficientConjugation U p)
  rw [← he, map_add, LinearMap.add_apply,
    rationalBilinear_antiholomorphic_isotropic H B hiso _ hcp _ hcp, add_zero] at hz
  have hpzero : p = 0 := by
    by_contra hne
    have h := hpos p hp hne
    rw [hz, mul_zero, Complex.zero_re] at h
    exact (lt_irrefl 0) h
  rw [hpzero, map_zero, zero_add] at he
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ U x).mp he.symm

def weightOnePolarizationOfPositive (H : WeightOne.CM.WeightOneHodgeStructure U)
    (B : LinearMap.BilinForm ℚ U) (hB : B.IsAlt)
    (hiso : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, B.baseChange ℂ u v = 0)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * B.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re) : CM.Polarization.WeightOnePolarization H where
  form := B
  alternating := hB
  nondegenerate := positiveAlternating_nondegenerate H B hB hiso hpos
  holomorphic_isotropic := hiso
  hodge_self_real := RationalBilinearConjugation.CM.Construction.rationalAlternating_hodge_self_real B hB
  hodge_positive := hpos

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm.CM.Construction
