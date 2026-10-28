import OAI.RepresentationTheory.Weil.Local.CharacterMeasure
import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Modulation Measure -/

namespace OAI.RepresentationTheory.Weil.Local.ModulationMeasure.Construction

noncomputable section

/-! Nontrivial local-field modulations determine finite measures. -/

open _root_.MeasureTheory BoundedContinuousFunction
open scoped BigOperators

variable {F : Type} [NormedField F] {d : ℕ}
def modulationCharacter (ψ : AddChar F ℂ) (p : FunctionsMetaplectic.Construction.Position F d) (x : FunctionsMetaplectic.Construction.Position F d) : ℂ :=
  ψ (FunctionsMetaplectic.Construction.dot p x)

theorem modulationCharacter_separates (ψ : AddChar F ℂ)
    (hψ : ∃ t, ψ t ≠ 1) (hunit : ∀ t, ‖ψ t‖ = 1)
    (x y : FunctionsMetaplectic.Construction.Position F d) (hxy : x ≠ y) :
    ∃ p, modulationCharacter ψ p x ≠ modulationCharacter ψ p y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨t, ht⟩ := hψ
  let p : FunctionsMetaplectic.Construction.Position F d := Pi.single i (t / (x i - y i))
  refine ⟨p, fun hh => ht ?_⟩
  have hp : FunctionsMetaplectic.Construction.dot p x - FunctionsMetaplectic.Construction.dot p y = t := by
    simp only [FunctionsMetaplectic.Construction.dot, p, Pi.single_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  rw [← hp, ψ.map_sub_eq_div]
  change ψ (FunctionsMetaplectic.Construction.dot p x) = ψ (FunctionsMetaplectic.Construction.dot p y) at hh
  rw [hh, div_self]
  intro hz
  have hn := hunit (FunctionsMetaplectic.Construction.dot p y)
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

variable (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
variable (hunit : ∀ t, ‖ψ t‖ = 1)

def boundedModulation (p : FunctionsMetaplectic.Construction.Position F d) : FunctionsMetaplectic.Construction.Position F d →ᵇ ℂ where
  toFun := modulationCharacter ψ p
  continuous_toFun := hψ.comp (by unfold FunctionsMetaplectic.Construction.dot; fun_prop)
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc
      dist _ _ ≤ ‖modulationCharacter ψ p x‖ + ‖modulationCharacter ψ p y‖ :=
        dist_le_norm_add_norm _ _
      _ = 2 := by rw [modulationCharacter, modulationCharacter, hunit, hunit]; norm_num

theorem boundedModulation_zero : boundedModulation ψ hψ hunit (0 : FunctionsMetaplectic.Construction.Position F d) = 1 := by
  ext x
  change ψ (FunctionsMetaplectic.Construction.dot 0 x) = 1
  simp [FunctionsMetaplectic.Construction.dot]

theorem boundedModulation_add (p q : FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (p + q) =
      boundedModulation ψ hψ hunit p * boundedModulation ψ hψ hunit q := by
  ext x
  change ψ (FunctionsMetaplectic.Construction.dot (p + q) x) = ψ (FunctionsMetaplectic.Construction.dot p x) * ψ (FunctionsMetaplectic.Construction.dot q x)
  simp [FunctionsMetaplectic.Construction.dot, add_mul, Finset.sum_add_distrib, ψ.map_add_eq_mul]

theorem boundedModulation_neg (p : FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (-p) = star (boundedModulation ψ hψ hunit p) := by
  ext x
  change ψ (FunctionsMetaplectic.Construction.dot (-p) x) = star (ψ (FunctionsMetaplectic.Construction.dot p x))
  have hp : FunctionsMetaplectic.Construction.dot (-p) x = -FunctionsMetaplectic.Construction.dot p x := by simp [FunctionsMetaplectic.Construction.dot]
  rw [hp, ψ.map_neg_eq_inv]
  exact Complex.inv_eq_conj (hunit _)

include hψ hunit in
theorem measures_eq_of_modulation_integrals
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hnontrivial : ∃ t, ψ t ≠ 1)
    (μ ν : Measure (FunctionsMetaplectic.Construction.Position F d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ p : FunctionsMetaplectic.Construction.Position F d,
      ∫ x, modulationCharacter ψ p x ∂μ = ∫ x, modulationCharacter ψ p x ∂ν) : μ = ν := by
  exact CharacterMeasure.measures_eq_of_character_integrals
    (boundedModulation ψ hψ hunit) (boundedModulation_zero ψ hψ hunit)
    (boundedModulation_add ψ hψ hunit) (boundedModulation_neg ψ hψ hunit)
    (modulationCharacter_separates ψ hnontrivial hunit) μ ν h

end

end OAI.RepresentationTheory.Weil.Local.ModulationMeasure.Construction
