import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient
import OAI.RepresentationTheory.Weil.UnitarySplitting.ProperQuadratic
import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Quadratic Norm Chart -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact

/-! Compactness of the norm-one group in an arbitrary nonsplit quadratic
algebra, with the actual product topology and units topology. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable {k : Type*} [Field k] (d : k)

abbrev NormOnePoint := {p : k × k | p.1 ^ 2 - d * p.2 ^ 2 = 1}

theorem quadratic_norm (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) : QuadraticAlgebra.norm z = z.re ^ 2 - d * z.im ^ 2 := by
  simp only [QuadraticAlgebra.norm_def]
  ring

def normOneOfPoint (p : NormOnePoint d) : QuadraticNormSquareQuotient.NormOne d := by
  let z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d := ⟨p.val.1, p.val.2⟩
  have hn : QuadraticAlgebra.norm z = 1 := (quadratic_norm d z).trans p.property
  have hm : z * star z = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn, map_one]
  exact ⟨⟨z, star z, hm, by rw [mul_comm]; exact hm⟩, Units.ext hn⟩

def normOnePointEquiv : QuadraticNormSquareQuotient.NormOne d ≃ NormOnePoint d where
  toFun p := ⟨(p.val.val.re, p.val.val.im), by
    exact (quadratic_norm d p.val.val).symm.trans (congrArg Units.val p.property)⟩
  invFun := normOneOfPoint d
  left_inv p := by
    apply Subtype.ext
    apply Units.ext
    exact QuadraticAlgebra.mk_eta p.val.val
  right_inv p := by
    apply Subtype.ext
    rfl

def normOnePointHomeomorph [TopologicalSpace k] [IsTopologicalRing k] : QuadraticNormSquareQuotient.NormOne d ≃ₜ NormOnePoint d where
  toEquiv := normOnePointEquiv d
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).comp (Units.continuous_val.comp continuous_subtype_val)).prodMk
      ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d).comp (Units.continuous_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Units.continuous_iff.mpr
    have hz : Continuous (fun p : NormOnePoint d => (⟨p.val.1, p.val.2⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) := by
      rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
      exact ⟨continuous_fst.comp continuous_subtype_val, continuous_snd.comp continuous_subtype_val⟩
    exact ⟨hz, continuous_star.comp hz⟩

theorem quadratic_polynomial_anisotropic (hns : ¬ IsSquare d) (p : k × k)
    (hp : p.1 ^ 2 - d * p.2 ^ 2 = 0) : p = 0 := by
  by_cases hy : p.2 = 0
  · have hx : p.1 = 0 := by simpa only [hy, zero_pow two_ne_zero, mul_zero, sub_zero,
      sq_eq_zero_iff] using hp
    exact Prod.ext hx hy
  · exfalso
    apply hns
    have he : (p.1 / p.2) ^ 2 = d := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hy)]
      linear_combination hp
    exact ⟨p.1 / p.2, by simpa only [pow_two] using he.symm⟩

theorem normOnePoint_isCompact
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (d : k) (hnd : ¬ DiscreteTopology k) (hns : ¬ IsSquare d) :
    IsCompact {p : k × k | p.1 ^ 2 - d * p.2 ^ 2 = 1} := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  · let : ProperSpace k := Weil.Local.FunctionsMetaplectic.Construction.localField_proper k hnd
    let q : k × k → k := fun p => p.1 ^ 2 - d * p.2 ^ 2
    have hc : Continuous q := by fun_prop
    have hhom : ∀ a : k, ∀ p : k × k, q (a • p) = a ^ 2 * q p := by
      intro a p
      change (a * p.1) ^ 2 - d * (a * p.2) ^ 2 = a ^ 2 * (p.1 ^ 2 - d * p.2 ^ 2)
      ring
    have hz : ∀ p, q p = 0 → p = 0 := quadratic_polynomial_anisotropic d hns
    have hproper := Weil.UnitarySplitting.ProperQuadratic.Construction.anisotropic_quadratic_isProperMap q hc hhom hz
    exact hproper.isCompact_preimage (isCompact_singleton : IsCompact ({1} : Set k))

theorem normOne_compactSpace
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (d : k) (hnd : ¬ DiscreteTopology k) (hns : ¬ IsSquare d) : CompactSpace (QuadraticNormSquareQuotient.NormOne d) := by
  let : CompactSpace (NormOnePoint d) := isCompact_iff_compactSpace.mp (normOnePoint_isCompact d hnd hns)
  exact (normOnePointHomeomorph d).symm.compactSpace

end RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact

namespace RepresentationTheory.Theta.Adelic.QuadraticNormChart

/-! Rational coordinates on the norm-one group for an arbitrary nonsplit
quadratic algebra. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact

variable {k : Type*} [Field k] (d : k)

theorem normOne_ext {p q : QuadraticNormSquareQuotient.NormOne d} (hr : p.val.val.re = q.val.val.re)
    (hi : p.val.val.im = q.val.val.im) : p = q := by
  apply Subtype.ext
  apply Units.ext
  exact QuadraticAlgebra.ext hr hi

theorem normOne_identity (p : QuadraticNormSquareQuotient.NormOne d) : p.val.val.re ^ 2 - d * p.val.val.im ^ 2 = 1 :=
  (Compact.normOnePointEquiv d p).property

def minusOne : QuadraticNormSquareQuotient.NormOne d := Compact.normOneOfPoint d ⟨(-1, 0), by simp⟩

theorem one_sub_mul_sq_ne_zero (hns : ¬ IsSquare d) (t : k) : 1 - d * t ^ 2 ≠ 0 := by
  intro he
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at he
  apply hns
  refine ⟨t⁻¹, ?_⟩
  field_simp
  linear_combination -he

def normChart (hns : ¬ IsSquare d) (t : k) : QuadraticNormSquareQuotient.NormOne d :=
  Compact.normOneOfPoint d ⟨((1 + d * t ^ 2) / (1 - d * t ^ 2), 2 * t / (1 - d * t ^ 2)), by
    change _ = 1
    field_simp [one_sub_mul_sq_ne_zero d hns t]
    ring⟩

def normCoordinate (p : QuadraticNormSquareQuotient.NormOne d) : k := p.val.val.im / (1 + p.val.val.re)

theorem normChart_zero (hns : ¬ IsSquare d) : normChart d hns 0 = 1 := by
  apply normOne_ext
  · change (1 + d * (0 : k) ^ 2) / (1 - d * (0 : k) ^ 2) = 1
    simp
  · change 2 * (0 : k) / (1 - d * (0 : k) ^ 2) = 0
    simp

theorem normChart_re_add_one [CharZero k] (hns : ¬ IsSquare d) (t : k) :
    1 + (normChart d hns t).val.val.re = 2 / (1 - d * t ^ 2) := by
  change 1 + (1 + d * t ^ 2) / (1 - d * t ^ 2) = 2 / (1 - d * t ^ 2)
  field_simp [one_sub_mul_sq_ne_zero d hns t]
  ring

theorem normChart_ne_minusOne [CharZero k] (hns : ¬ IsSquare d) (t : k) :
    normChart d hns t ≠ minusOne d := by
  intro he
  have hx := normChart_re_add_one d hns t
  rw [he] at hx
  change 1 + (-1 : k) = 2 / (1 - d * t ^ 2) at hx
  have ht : (2 : k) / (1 - d * t ^ 2) ≠ 0 := div_ne_zero (by norm_num)
    (one_sub_mul_sq_ne_zero d hns t)
  exact ht (by simpa using hx.symm)

theorem normCoordinate_chart [CharZero k] (hns : ¬ IsSquare d) (t : k) :
    normCoordinate d (normChart d hns t) = t := by
  rw [normCoordinate, normChart_re_add_one]
  change (2 * t / (1 - d * t ^ 2)) / (2 / (1 - d * t ^ 2)) = t
  have hd : 1 - t ^ 2 * d ≠ 0 := by simpa only [mul_comm] using one_sub_mul_sq_ne_zero d hns t
  field_simp [one_sub_mul_sq_ne_zero d hns t, hd]

theorem normOne_re_ne_neg_one (hns : ¬ IsSquare d) (p : QuadraticNormSquareQuotient.NormOne d) (hp : p ≠ minusOne d) :
    1 + p.val.val.re ≠ 0 := by
  intro he
  have hx : p.val.val.re = -1 := by linear_combination he
  have hn := normOne_identity d p
  rw [hx] at hn
  have hd : d ≠ 0 := by
    rintro rfl
    exact hns ⟨0, by simp⟩
  have hy2 : p.val.val.im ^ 2 = 0 := by
    apply (mul_eq_zero.mp (show d * p.val.val.im ^ 2 = 0 from by linear_combination -hn)).resolve_left hd
  have hy : p.val.val.im = 0 := sq_eq_zero_iff.mp hy2
  exact hp (normOne_ext d hx hy)

theorem normChart_coordinate [CharZero k] (hns : ¬ IsSquare d) (p : QuadraticNormSquareQuotient.NormOne d)
    (hp : p ≠ minusOne d) : normChart d hns (normCoordinate d p) = p := by
  have hd := normOne_re_ne_neg_one d hns p hp
  have hn := normOne_identity d p
  have he : 1 - d * (p.val.val.im / (1 + p.val.val.re)) ^ 2 = 2 / (1 + p.val.val.re) := by
    field_simp
    linear_combination hn
  apply normOne_ext
  · change (1 + d * (p.val.val.im / (1 + p.val.val.re)) ^ 2) /
      (1 - d * (p.val.val.im / (1 + p.val.val.re)) ^ 2) = p.val.val.re
    rw [he]
    field_simp
    linear_combination -hn
  · change (2 * (p.val.val.im / (1 + p.val.val.re))) /
      (1 - d * (p.val.val.im / (1 + p.val.val.re)) ^ 2) = p.val.val.im
    rw [he]
    field_simp

theorem normChart_continuous [TopologicalSpace k] [IsTopologicalDivisionRing k]
    (hns : ¬ IsSquare d) : Continuous (normChart d hns) := by
  have hpoint : Continuous (fun t : k =>
      (⟨((1 + d * t ^ 2) / (1 - d * t ^ 2), 2 * t / (1 - d * t ^ 2)),
        (Compact.normOnePointEquiv d (normChart d hns t)).property⟩ : Compact.NormOnePoint d)) := by
    apply Continuous.subtype_mk
    exact ((continuous_const.add (continuous_const.mul (continuous_id.pow 2))).div
      (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))) (one_sub_mul_sq_ne_zero d hns)).prodMk
      ((continuous_const.mul continuous_id).div
        (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))) (one_sub_mul_sq_ne_zero d hns))
  exact (Compact.normOnePointHomeomorph d).symm.continuous.comp hpoint

theorem normCoordinate_continuousAt [TopologicalSpace k] [IsTopologicalDivisionRing k]
    (hns : ¬ IsSquare d) (p : QuadraticNormSquareQuotient.NormOne d) (hp : p ≠ minusOne d) : ContinuousAt (normCoordinate d) p := by
  have hr : Continuous (fun p : QuadraticNormSquareQuotient.NormOne d => p.val.val.re) :=
    (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).comp (Units.continuous_val.comp continuous_subtype_val)
  have hi : Continuous (fun p : QuadraticNormSquareQuotient.NormOne d => p.val.val.im) :=
    (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d).comp (Units.continuous_val.comp continuous_subtype_val)
  exact hi.continuousAt.div (continuous_const.add hr).continuousAt (normOne_re_ne_neg_one d hns p hp)

end RepresentationTheory.Theta.Adelic.QuadraticNormChart

end

end OAI
