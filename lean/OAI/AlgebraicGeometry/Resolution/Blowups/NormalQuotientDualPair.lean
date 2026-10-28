import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift
import OAI.AlgebraicGeometry.Resolution.Blowups.DualPairBlowupSmooth

/-! # Normal Quotient Dual Pair -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDualPair.Construction

noncomputable section

/-! Normalize a lifted quotient coordinate to an exact dual derivation pair. -/

theorem exists_dual_pair_of_transverse_unit
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (z g : R) (D E : Derivation k R R) (hDz : D z = 1) (hEz : E z = 0) (hEg : IsUnit (E g)) :
    ∃ D' E' : Derivation k R R, D' z = 1 ∧ D' g = 0 ∧ E' z = 0 ∧ E' g = 1 := by
  obtain ⟨a, ha⟩ := hEg
  let E' : Derivation k R R := (↑(a⁻¹) : R) • E
  have hE'z : E' z = 0 := by simp only [E', Derivation.smul_apply, smul_eq_mul, hEz, mul_zero]
  have hE'g : E' g = 1 := by
    change (↑(a⁻¹) : R) * E g = 1
    rw [← ha, Units.inv_mul]
  refine ⟨D - D g • E', E', ?_, ?_, hE'z, hE'g⟩
  · simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hDz, hE'z, mul_zero, sub_zero]
  · simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hE'g, mul_one, sub_self]

theorem span_normal_pair_eq_top_of_quotient_one
    {R : Type*} [CommRing R] (z a : R) (h : Ideal.Quotient.mk (Ideal.span {z}) a = 1) :
    Ideal.span {z, a} = ⊤ := by
  have hs : a - 1 ∈ Ideal.span {z} := Ideal.Quotient.eq_zero_iff_mem.mp (by
    rw [map_sub, h, map_one, sub_self])
  have hz : Ideal.span {z} ≤ Ideal.span {z, a} := Ideal.span_mono (by simp)
  have ha : a ∈ Ideal.span {z, a} := Ideal.subset_span (by simp)
  have h1 : (1 : R) ∈ Ideal.span {z, a} := by
    convert (Ideal.span {z, a}).sub_mem ha (hz hs) using 1
    ring
  exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDualPair.Construction
