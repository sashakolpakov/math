import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Finite Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteCharacter.CM

noncomputable section

/-! The finite additive character of a number field, constructed from
rational representatives and the field trace, with no character input. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable (F : Type) [Field F] [NumberField F]

theorem exists_representative (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∃ r : F, a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F :=
  (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).exists_mem_open
    (s := {b : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F | a - b ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F})
    ((RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage (continuous_const.sub continuous_id)) ⟨a, by simp⟩

def representative (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : F := (exists_representative F a).choose

theorem representative_spec (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (representative F a) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F :=
  (exists_representative F a).choose_spec

theorem trace_integer (r : 𝓞 F) : ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ F (r : F) := by
  have ht : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) := Algebra.isIntegral_trace r.property
  exact IsIntegrallyClosed.isIntegral_iff.mp ht

def phase (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : ℂ :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F (representative F a) : ℝ))

theorem phase_of_representative (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (q : F)
    (hq : a - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) :
    phase F a = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F q : ℝ)) := by
  have hint : algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (representative F a - q) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F := by
    have h := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).sub_mem hq (representative_spec F a)
    convert h using 1
    simp only [map_sub]
    ring
  obtain ⟨r, hr⟩ := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F _).mp hint
  obtain ⟨n, hn⟩ := trace_integer F r
  have hn' : (n : ℚ) = Algebra.trace ℚ F (representative F a) - Algebra.trace ℚ F q := by
    rw [← map_sub, ← hr]
    exact hn
  have he : -(Algebra.trace ℚ F (representative F a) : ℝ) =
      -(Algebra.trace ℚ F q : ℝ) + ((-n : ℤ) : ℝ) := by
    have hnR : (n : ℝ) = (Algebra.trace ℚ F (representative F a) : ℝ) - (Algebra.trace ℚ F q : ℝ) := by
      exact_mod_cast hn'
    push_cast
    linarith
  rw [phase, he, AddChar.map_add_eq_mul, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_intCast, mul_one]

def character : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ℂ where
  toFun := phase F
  map_zero_eq_one' := by
    rw [phase_of_representative F 0 0 (by simp)]
    simp
  map_add_eq_mul' a b := by
    have h : a + b - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
        (representative F a + representative F b) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F := by
      have h := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).add_mem (representative_spec F a) (representative_spec F b)
      convert h using 1
      simp only [map_add]
      ring
    rw [phase_of_representative F _ _ h, map_add, Rat.cast_add, neg_add, AddChar.map_add_eq_mul]
    rfl

theorem character_rational (q : F) :
    character F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(Algebra.trace ℚ F q : ℝ)) :=
  phase_of_representative F _ q (by simp)

theorem character_unitary (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : ‖character F a‖ = 1 :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary _

theorem character_locallyConstant : IsLocallyConstant (character F : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F → ℂ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  refine ⟨{b | b - a ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F},
    (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage (continuous_id.sub continuous_const), by simp, ?_⟩
  intro b hb
  have h : b - algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (representative F a) ∈ RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F := by
    have h := (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).add_mem hb (representative_spec F a)
    simpa only [sub_add_sub_cancel] using h
  exact phase_of_representative F b (representative F a) h

theorem character_continuous : Continuous (character F : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F → ℂ) :=
  (character_locallyConstant F).continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteCharacter.CM
