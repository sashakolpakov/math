import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Adelic Character -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter.CM.Finite

/-! Construct the finite adelic additive character from rational
representatives modulo the integral adeles. Independence of the
representative, continuity, and the exact conductor are proved here;
no Weil data or additive character is an input. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

def representative (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ℚ :=
  Classical.choose (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteAdele_rational_representative a)

theorem representative_spec (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (representative a) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  Classical.choose_spec (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteAdele_rational_representative a)

def phase (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ℂ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(representative a : ℝ))

theorem phase_of_representative (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (q : ℚ)
    (hq : a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    phase a = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) := by
  have hint : algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (representative a - q) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
    have h := RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sub_mem hq (representative_spec a)
    convert h using 1
    simp only [map_sub]
    ring
  obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff _).mp hint
  have he : -(representative a : ℝ) = -(q : ℝ) + ((-n : ℤ) : ℝ) := by
    have hn' : (n : ℝ) = (representative a : ℝ) - (q : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  rw [phase, he, AddChar.map_add_eq_mul, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_intCast, mul_one]

def character : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ where
  toFun := phase
  map_zero_eq_one' := by
    rw [phase_of_representative 0 0 (by simp)]
    simp
  map_add_eq_mul' a b := by
    have h : a + b - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (representative a + representative b) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
      have h := RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem (representative_spec a) (representative_spec b)
      convert h using 1
      simp only [map_add]
      ring
    rw [phase_of_representative _ _ h, Rat.cast_add, neg_add, AddChar.map_add_eq_mul]
    rfl

theorem character_of_representative (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (q : ℚ)
    (hq : a - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    character a = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) :=
  phase_of_representative a q hq

theorem character_rational (q : ℚ) :
    character (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) :=
  character_of_representative _ q (by simp)

theorem character_integral (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) : character a = 1 := by
  rw [character_of_representative a 0 (by simpa using ha)]
  simp

theorem character_unitary (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ‖character a‖ = 1 :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary _

theorem character_locallyConstant : IsLocallyConstant (character : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf → ℂ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  refine ⟨{b | b - a ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele},
    RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage (continuous_id.sub continuous_const), by simp, ?_⟩
  intro b hb
  have h : b - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (representative a) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
    have h := RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem hb (representative_spec a)
    simpa only [sub_add_sub_cancel] using h
  exact character_of_representative b (representative a) h

theorem character_continuous : Continuous (character : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf → ℂ) :=
  character_locallyConstant.continuous

theorem character_eq_one_iff (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : character a = 1 ↔ a ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  refine ⟨fun ha => ?_, character_integral a⟩
  obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_eq_one_iff _).mp ha
  have hnq : (n : ℚ) = -representative a := by exact_mod_cast hn
  have hr : algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (representative a) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
    apply (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff _).mpr
    exact ⟨-n, by push_cast; linarith⟩
  simpa only [sub_add_cancel] using RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem (representative_spec a) hr

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter.CM.Finite

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter.CM

/-! The standard character on the actual rational adeles, with its
archimedean normalization and triviality on diagonal rational points. -/

def character : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ ℂ where
  toFun x := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter x.1 * Finite.character x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

theorem character_apply (x : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    character x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter x.1 * Finite.character x.2 := rfl

theorem character_continuous : Continuous (character : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ → ℂ) := by
  have hr : Continuous (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter : ℝ → ℂ) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  exact (hr.comp continuous_fst).mul
    (Finite.character_continuous.comp continuous_snd)

theorem character_unitary (x : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) : ‖character x‖ = 1 := by
  rw [character_apply, norm_mul, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary,
    Finite.character_unitary, mul_one]

theorem character_rational (q : ℚ) : character (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ q) = 1 := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (q : ℝ) *
    Finite.character (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) = 1
  rw [Finite.character_rational,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem character_real (t : ℝ) : character (t, 0) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter t := by
  rw [character_apply, AddChar.map_zero_eq_one, mul_one]

theorem character_finite (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    character (0, a) = Finite.character a := by
  rw [character_apply, AddChar.map_zero_eq_one, one_mul]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter.CM

end

end OAI
