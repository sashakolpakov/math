import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-! # Norm Denominator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.NormDenominator

noncomputable section

/-! The determinant of multiplication supplies an integral factor for
an inverse. An integral element congruent to one modulo the level has
an integer determinant congruent to one modulo the same level.
-/

section Basis

variable {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype I] [DecidableEq I] (b : Module.Basis I R A)

def integralAdjugateFactor (x : A) : A :=
  b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate.mulVec (b.equivFun 1))

theorem mul_integralAdjugateFactor (x : A) :
    x * integralAdjugateFactor b x = (Algebra.leftMulMatrix b x).det • (1 : A) := by
  apply b.equivFun.injective
  calc
    b.equivFun (x * integralAdjugateFactor b x) =
        (Algebra.leftMulMatrix b x).mulVec (b.equivFun (integralAdjugateFactor b x)) := by
      simpa only [Module.Basis.equivFun_apply] using
        (Algebra.leftMulMatrix_mulVec_repr b x (integralAdjugateFactor b x)).symm
    _ = (Algebra.leftMulMatrix b x).mulVec
        ((Algebra.leftMulMatrix b x).adjugate.mulVec (b.equivFun 1)) := by
      rw [integralAdjugateFactor, LinearEquiv.apply_symm_apply]
    _ = (Algebra.leftMulMatrix b x).det • b.equivFun (1 : A) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = b.equivFun ((Algebra.leftMulMatrix b x).det • (1 : A)) :=
      (b.equivFun.map_smul _ _).symm

theorem leftMulMatrix_det_congruent_one
    {T : Type*} [CommRing T] (f : R →+* T) (ℓ : R) (hℓ : f ℓ = 0) (t : A) :
    f (Algebra.leftMulMatrix b (1 + ℓ • t)).det = 1 := by
  have hm : (Algebra.leftMulMatrix b (1 + ℓ • t)).map f = 1 := by
    rw [map_add, map_one, map_smul]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, h, hℓ]
  rw [RingHom.map_det]
  change ((Algebra.leftMulMatrix b (1 + ℓ • t)).map f).det = 1
  rw [hm, Matrix.det_one]

end Basis

variable (E : Type*) [Field E] [NumberField E]

theorem integral_element_congruent_one_integer_denominator
    (ℓ : ℕ) (t : NumberField.RingOfIntegers E)
    (hx : (1 + (ℓ : NumberField.RingOfIntegers E) * t) ≠ 0) :
    ∃ d : ℤ, d ≠ 0 ∧ (ℓ : ℤ) ∣ d - 1 ∧
      ∃ a : NumberField.RingOfIntegers E,
        (1 + (ℓ : E) * (t : E)) * (a : E) = (d : E) := by
  classical
  let b := Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers E)
  let x : NumberField.RingOfIntegers E := 1 + (ℓ : NumberField.RingOfIntegers E) * t
  let d : ℤ := (Algebra.leftMulMatrix b x).det
  have hd : d ≠ 0 := by
    rw [show d = Algebra.norm ℤ x from (Algebra.norm_eq_matrix_det b x).symm]
    exact Algebra.norm_ne_zero_iff.mpr hx
  have hmod : (d : ZMod ℓ) = 1 := by
    have h := leftMulMatrix_det_congruent_one b (Int.castRingHom (ZMod ℓ)) (ℓ : ℤ)
      (by simp) t
    simpa only [d, x, Algebra.smul_def, map_natCast, eq_intCast] using h
  have hdiv : (ℓ : ℤ) ∣ d - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (d - 1) ℓ).mp
    rw [Int.cast_sub, Int.cast_one, hmod, sub_self]
  refine ⟨d, hd, hdiv, integralAdjugateFactor b x, ?_⟩
  have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E)
    (mul_integralAdjugateFactor b x)
  simpa only [x, d, map_mul, map_add, map_one, map_natCast, Algebra.smul_def,
    mul_one, eq_intCast, map_intCast, NumberField.RingOfIntegers.coe_eq_algebraMap] using h

theorem integral_element_congruent_one_positive_coprime_denominator
    (ℓ : ℕ) (t : NumberField.RingOfIntegers E)
    (hx : (1 + (ℓ : NumberField.RingOfIntegers E) * t) ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ Nat.Coprime D ℓ ∧
      (ℓ : ℤ) ∣ (D : ℤ) - 1 ∧
      ∃ a : NumberField.RingOfIntegers E,
        (1 + (ℓ : E) * (t : E)) * (a : E) = (D : E) := by
  obtain ⟨d, hd, hdiv, a, ha⟩ :=
    integral_element_congruent_one_integer_denominator E ℓ t hx
  have hcoprime : IsCoprime d (ℓ : ℤ) := by
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨1, -k, ?_⟩
    rw [one_mul, neg_mul, mul_comm k, ← hk]
    ring
  have hnat : Nat.Coprime d.natAbs ℓ := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using
      (Int.isCoprime_iff_gcd_eq_one.mp hcoprime)
  have hcastZ : ((d.natAbs ^ 2 : ℕ) : ℤ) = d ^ 2 := by
    simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  have hcast : ((d.natAbs ^ 2 : ℕ) : E) = (d : E) ^ 2 := by
    simpa only [Int.cast_natCast, Int.cast_pow] using congrArg (fun z : ℤ => (z : E)) hcastZ
  have hsqdiv : (ℓ : ℤ) ∣ ((d.natAbs ^ 2 : ℕ) : ℤ) - 1 := by
    rw [hcastZ]
    exact hdiv.trans (by simpa only [one_pow] using sub_dvd_pow_sub_pow d (1 : ℤ) 2)
  refine ⟨d.natAbs ^ 2, pow_pos (Int.natAbs_pos.mpr hd) 2, hnat.pow_left 2,
    hsqdiv, (d : NumberField.RingOfIntegers E) * a, ?_⟩
  change (1 + (ℓ : E) * (t : E)) * ((d : E) * (a : E)) = _
  rw [hcast]
  calc
    (1 + (ℓ : E) * (t : E)) * ((d : E) * (a : E)) =
        (d : E) * ((1 + (ℓ : E) * (t : E)) * (a : E)) := by ring
    _ = (d : E) ^ 2 := by rw [ha, pow_two]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.NormDenominator
