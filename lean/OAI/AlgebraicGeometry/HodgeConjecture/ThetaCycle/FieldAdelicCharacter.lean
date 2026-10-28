import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanTrace
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient

/-! # Field Adelic Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM

noncomputable section

/-! ThetaCycle: the standard trace character on the actual number-field adeles.
The finite part is constructed by strong approximation and the archimedean
part is the real-linear extension of the field trace. -/

open scoped Classical _root_.Topology _root_.NumberField
open _root_.NumberField OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction Filter

variable (F : Type) [Field F] [NumberField F]

def fieldFiniteRepresentative (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : F :=
  (RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction.exists_rational_finite_integral_remainder F a).choose

theorem field_finite_representative_spec (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F a) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F :=
  (RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction.exists_rational_finite_integral_remainder F a).choose_spec

theorem negative_trace_character_eq (q r : F)
    (h : algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (q - r) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F q : ℝ)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F r : ℝ)) := by
  obtain ⟨s, hs⟩ := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F (q - r)).mp h
  obtain ⟨n, hn⟩ := ArchimedeanTrace.CM.field_trace_integer F s
  have he : (Algebra.trace ℚ F q : ℝ) = (n : ℝ) + (Algebra.trace ℚ F r : ℝ) := by
    have ht : (n : ℚ) = Algebra.trace ℚ F q - Algebra.trace ℚ F r := by
      rw [← map_sub, ← hs]
      exact hn
    exact_mod_cast (sub_eq_iff_eq_add.mp ht.symm)
  rw [he, neg_add, AddChar.map_add_eq_mul]
  have hi : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(n : ℝ)) = 1 := by
    simpa only [Int.cast_neg] using RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_intCast (-n)
  rw [hi, one_mul]

def fieldFiniteCharacterValue (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : ℂ :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F (fieldFiniteRepresentative F a) : ℝ))

theorem field_finite_character_representative (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (q : F)
    (hq : a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) :
    fieldFiniteCharacterValue F a = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F q : ℝ)) := by
  apply negative_trace_character_eq F
  have he : algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F a - q) =
      (a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) -
        (a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F a)) := by
    rw [map_sub]
    abel
  rw [he]
  exact (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).sub_mem hq (field_finite_representative_spec F a)

def fieldFiniteCharacter : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ℂ where
  toFun := fieldFiniteCharacterValue F
  map_zero_eq_one' := by
    rw [field_finite_character_representative F 0 0 (by simp)]
    simp
  map_add_eq_mul' a b := by
    have h := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).add_mem (field_finite_representative_spec F a)
      (field_finite_representative_spec F b)
    have he : a + b - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
        (fieldFiniteRepresentative F a + fieldFiniteRepresentative F b) =
        (a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F a)) +
          (b - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F b)) := by
      rw [map_add]
      abel
    rw [field_finite_character_representative F (a + b) _ (he ▸ h)]
    simp only [map_add, Rat.cast_add, neg_add, AddChar.map_add_eq_mul, fieldFiniteCharacterValue]

theorem field_finite_character_rational (q : F) :
    fieldFiniteCharacter F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F q : ℝ)) :=
  field_finite_character_representative F _ q (by simp)

theorem field_finite_character_integral (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (ha : a ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) :
    fieldFiniteCharacter F a = 1 := by
  change fieldFiniteCharacterValue F a = 1
  rw [field_finite_character_representative F a 0 (by simpa using ha)]
  simp

theorem field_finite_character_locallyConstant : IsLocallyConstant (fieldFiniteCharacter F) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have hU : IsOpen {b : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F |
      b - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (fieldFiniteRepresentative F a) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F} :=
    (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage (continuous_id.sub continuous_const)
  filter_upwards [hU.mem_nhds (field_finite_representative_spec F a)] with b hb
  exact field_finite_character_representative F b (fieldFiniteRepresentative F a) hb

theorem field_finite_character_unitary (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : ‖fieldFiniteCharacter F a‖ = 1 :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary _

def fieldAdelicCharacter : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ where
  toFun a := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F a.1) * fieldFiniteCharacter F a.2
  map_zero_eq_one' := by
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F 0) * fieldFiniteCharacter F 0 = 1
    simp
  map_add_eq_mul' a b := by
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F (a.1 + b.1)) * fieldFiniteCharacter F (a.2 + b.2) = _
    simp only [map_add, AddChar.map_add_eq_mul]
    ring

theorem field_adelic_character_infinite (t : InfiniteAdeleRing F) :
    fieldAdelicCharacter F (t, 0) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F t) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F t) * fieldFiniteCharacter F 0 = _
  simp

theorem field_adelic_character_finite (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    fieldAdelicCharacter F (0, a) = fieldFiniteCharacter F a := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F 0) * fieldFiniteCharacter F a = _
  simp

theorem field_adelic_character_principal (q : F) :
    fieldAdelicCharacter F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1 := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F (algebraMap F (InfiniteAdeleRing F) q)) *
    fieldFiniteCharacter F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = 1
  rw [ArchimedeanTrace.CM.infinite_field_trace_rational, field_finite_character_rational, ← AddChar.map_add_eq_mul]
  simp

theorem field_adelic_character_continuous : Continuous (fieldAdelicCharacter F) := by
  have hr : Continuous RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter := by
    change Continuous (fun t : ℝ => ((Real.fourierChar t : Circle) : ℂ))
    exact continuous_subtype_val.comp Real.continuous_fourierChar
  exact ((hr.comp (ArchimedeanTrace.CM.infinite_field_trace_continuous F)).comp continuous_fst).mul
    ((field_finite_character_locallyConstant F).continuous.comp continuous_snd)

theorem field_adelic_character_unitary (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) : ‖fieldAdelicCharacter F a‖ = 1 := by
  change ‖RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.infiniteFieldTrace F a.1) * fieldFiniteCharacter F a.2‖ = 1
  rw [norm_mul, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary, field_finite_character_unitary, one_mul]

theorem field_adelic_character_nontrivial : ∃ a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, fieldAdelicCharacter F a ≠ 1 := by
  let q : F := algebraMap ℚ F (1 / (2 * (Module.finrank ℚ F : ℚ)))
  have hd : (Module.finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos : 0 < Module.finrank ℚ F))
  have hq : Algebra.trace ℚ F q = 1 / 2 := by
    change Algebra.trace ℚ F (algebraMap ℚ F _) = _
    rw [Algebra.trace_algebraMap, nsmul_eq_mul]
    field_simp
  refine ⟨(algebraMap F (InfiniteAdeleRing F) q, 0), ?_⟩
  rw [field_adelic_character_infinite, ArchimedeanTrace.CM.infinite_field_trace_rational, hq]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  intro h
  obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_eq_one_iff (1 / 2)).mp h
  have hpos : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) by rw [hn]; norm_num)
  have hlt : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by rw [hn]; norm_num)
  omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM
