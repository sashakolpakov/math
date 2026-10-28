import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Adelic Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicCharacter.CM

noncomputable section

/-! ThetaCycle: construct the standard additive character on the actual rational
adeles. Finite representatives modulo the integral adeles supply its finite
part; no Weil representation or character package is assumed. -/

open scoped Classical _root_.Topology
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction Filter

def finiteRationalRepresentative (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ℚ := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteAdele_rational_representative a).choose

theorem finite_rational_representative_spec (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteAdele_rational_representative a).choose_spec

theorem negative_rational_character_eq (q r : ℚ)
    (h : algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (q - r) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(r : ℝ)) := by
  obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff (q - r)).mp h
  have he : (q : ℝ) = (n : ℝ) + (r : ℝ) := by
    exact_mod_cast (sub_eq_iff_eq_add.mp hn.symm)
  rw [he, neg_add, AddChar.map_add_eq_mul]
  have hi : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(n : ℝ)) = 1 := by
    simpa only [Int.cast_neg] using RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_intCast (-n)
  rw [hi, one_mul]

def finiteStandardCharacterValue (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ℂ :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(finiteRationalRepresentative a : ℝ))

theorem finite_standard_character_representative (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (q : ℚ)
    (hq : a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    finiteStandardCharacterValue a = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) := by
  apply negative_rational_character_eq
  have he : algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a - q) =
      (a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) - (a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a)) := by
    rw [map_sub]
    abel
  rw [he]
  exact RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sub_mem hq (finite_rational_representative_spec a)

def finiteStandardCharacter : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ where
  toFun := finiteStandardCharacterValue
  map_zero_eq_one' := by
    rw [finite_standard_character_representative 0 0 (by simp)]
    simp
  map_add_eq_mul' a b := by
    have h := RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem (finite_rational_representative_spec a)
      (finite_rational_representative_spec b)
    have he : a + b - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a + finiteRationalRepresentative b) =
        (a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a)) +
          (b - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative b)) := by
      rw [map_add]
      abel
    rw [finite_standard_character_representative (a + b) _ (he ▸ h)]
    simp only [Rat.cast_add, neg_add, AddChar.map_add_eq_mul, finiteStandardCharacterValue]

theorem finite_standard_character_rational (q : ℚ) :
    finiteStandardCharacter (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) :=
  finite_standard_character_representative _ q (by simp)

theorem finite_standard_character_integral (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    finiteStandardCharacter a = 1 := by
  change finiteStandardCharacterValue a = 1
  rw [finite_standard_character_representative a 0 (by simpa using ha)]
  simp

theorem finite_standard_character_locallyConstant : IsLocallyConstant finiteStandardCharacter := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have hU : IsOpen {b : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | b - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (finiteRationalRepresentative a) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele} :=
    RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage (continuous_id.sub continuous_const)
  filter_upwards [hU.mem_nhds (finite_rational_representative_spec a)] with b hb
  exact finite_standard_character_representative b (finiteRationalRepresentative a) hb

theorem finite_standard_character_unitary (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ‖finiteStandardCharacter a‖ = 1 :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary _

def rationalAdelicCharacter : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ ℂ where
  toFun a := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter a.1 * finiteStandardCharacter a.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

theorem rational_adelic_character_real (t : ℝ) :
    rationalAdelicCharacter (t, 0) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter t := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter t * finiteStandardCharacter 0 = _
  simp

theorem rational_adelic_character_finite (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    rationalAdelicCharacter (0, a) = finiteStandardCharacter a := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter 0 * finiteStandardCharacter a = _
  simp

theorem rational_adelic_character_principal (q : ℚ) :
    rationalAdelicCharacter (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ q) = 1 := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (q : ℝ) * finiteStandardCharacter (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) = 1
  rw [finite_standard_character_rational, ← AddChar.map_add_eq_mul]
  simp

theorem rational_adelic_character_continuous : Continuous rationalAdelicCharacter := by
  have hr : Continuous RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter := by
    change Continuous (fun t : ℝ => ((Real.fourierChar t : Circle) : ℂ))
    exact continuous_subtype_val.comp Real.continuous_fourierChar
  exact (hr.comp continuous_fst).mul (finite_standard_character_locallyConstant.continuous.comp continuous_snd)

theorem rational_adelic_character_unitary (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) : ‖rationalAdelicCharacter a‖ = 1 := by
  change ‖RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter a.1 * finiteStandardCharacter a.2‖ = 1
  rw [norm_mul, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary, finite_standard_character_unitary, one_mul]

theorem rational_adelic_character_nontrivial : ∃ a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ, rationalAdelicCharacter a ≠ 1 := by
  refine ⟨(1 / 2, 0), ?_⟩
  rw [rational_adelic_character_real]
  intro h
  obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_eq_one_iff (1 / 2)).mp h
  have hpos : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) by rw [hn]; norm_num)
  have hlt : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by rw [hn]; norm_num)
  omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicCharacter.CM
