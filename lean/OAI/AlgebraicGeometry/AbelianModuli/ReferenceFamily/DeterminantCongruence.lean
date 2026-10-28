import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitaryDeterminant
import OAI.NumberTheory.ArithmeticGroups.Congruence

/-! # Determinant Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence

noncomputable section

/-! Determinants preserve integral matrix congruences. A determinant
congruent to one at level at least three and having CM norm one is one,
using the proved torsion-unit and integral-congruence theorems. -/

open scoped Classical _root_.NumberField

theorem determinant_one_add {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (m : R) (B : Matrix I I R) :
    ∃ a : R, (1 + m • B).det = 1 + m * a := by
  let J : Ideal R := Ideal.span {m}
  let q := Ideal.Quotient.mk J
  have hm : q m = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton m))
  have he : (1 + m • B).map q = 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hm, zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]
  have hdet : q ((1 + m • B).det - 1) = 0 := by
    rw [map_sub]
    have hmap : q (1 + m • B).det = ((1 + m • B).map q).det := q.map_det _
    rw [hmap, he, Matrix.det_one, map_one, sub_self]
  have hdiv : m ∣ (1 + m • B).det - 1 :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hdet)
  obtain ⟨a, ha⟩ := hdiv
  exact ⟨a, (eq_add_of_sub_eq ha).trans (add_comm _ _)⟩

theorem integral_matrix_determinant_congruence {E I : Type*} [Field E] [NumberField E]
    [Fintype I] [DecidableEq I] (M : Matrix I I E) (m : ℕ)
    (hM : ∀ i j, ∃ a : E, IsIntegral ℤ a ∧ M i j - (1 : Matrix I I E) i j = (m : E) * a) :
    ∃ a : E, IsIntegral ℤ a ∧ M.det = 1 + (m : E) * a := by
  choose a ha h using hM
  let B : Matrix I I (𝓞 E) := fun i j => ⟨a i j, ha i j⟩
  let inc : (𝓞 E) →+* E := algebraMap (𝓞 E) E
  have he : M = (1 + (m : 𝓞 E) • B).map inc := by
    ext i j
    change M i j = inc ((1 : Matrix I I (𝓞 E)) i j + (m : 𝓞 E) * B i j)
    rw [map_add, map_mul, map_natCast]
    have hi : inc ((1 : Matrix I I (𝓞 E)) i j) = (1 : Matrix I I E) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero]
    rw [hi]
    exact (eq_add_of_sub_eq (h i j)).trans (add_comm _ _)
  obtain ⟨b, hb⟩ := determinant_one_add (m : 𝓞 E) B
  refine ⟨(b : E), b.property, ?_⟩
  have hdet : M.det = inc (1 + (m : 𝓞 E) • B).det :=
    (congrArg Matrix.det he).trans (inc.map_det _).symm
  rw [hdet, hb, map_add, map_one, map_mul, map_natCast]

theorem norm_one_integral_congruence_eq_one {E : Type*} [Field E] [NumberField E]
    [NumberField.IsCMField E] (z a : E) (ha : IsIntegral ℤ a)
    (N : ℕ) (hN : 3 ≤ N) (hz : z = 1 + (N : E) * a)
    (hnorm : z * NumberField.IsCMField.complexConj E z = 1) : z = 1 := by
  have hint : IsIntegral ℤ z := hz ▸ (isIntegral_one.add ((isIntegral_natCast N).mul ha))
  let zO : 𝓞 E := ⟨z, hint⟩
  let w := NumberField.IsCMField.ringOfIntegersComplexConj E zO
  have hw : zO * w = 1 := by
    apply Subtype.ext
    exact hnorm
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne zO w hw
  obtain ⟨k, hk, hp⟩ := NumberTheory.CMField.NormOneUnits.norm_one_unit_is_root_of_unity u hnorm
  have hpow : z ^ k = 1 := congrArg (fun v : (𝓞 E)ˣ => ((v : 𝓞 E) : E)) hp
  have ha0 : a = 0 := NumberTheory.ArithmeticGroups.Congruence.Level.integral_root_of_unity_congruence a ha N hN k hk (hz ▸ hpow)
  simpa only [ha0, mul_zero, add_zero] using hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence
