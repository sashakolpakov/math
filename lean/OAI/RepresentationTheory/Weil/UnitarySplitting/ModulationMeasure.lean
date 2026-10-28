import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterMeasure

/-! # Modulation Measure -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ModulationMeasure.Construction

noncomputable section

/-! Nontrivial local-field modulations determine finite measures. -/

open _root_.MeasureTheory BoundedContinuousFunction
open scoped BigOperators

variable {F : Type} [NormedField F] {d : ℕ}
variable (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
variable (hunit : ∀ t, ‖ψ t‖ = 1)

def boundedModulation (p : Local.FunctionsMetaplectic.Construction.Position F d) : Local.FunctionsMetaplectic.Construction.Position F d →ᵇ ℂ where
  toFun := UltraMultiplier.Construction.modulationCharacter ψ p
  continuous_toFun := hψ.comp (by unfold Local.FunctionsMetaplectic.Construction.dot; fun_prop)
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc
      dist _ _ ≤ ‖UltraMultiplier.Construction.modulationCharacter ψ p x‖ + ‖UltraMultiplier.Construction.modulationCharacter ψ p y‖ :=
        dist_le_norm_add_norm _ _
      _ = 2 := by rw [UltraMultiplier.Construction.modulationCharacter, UltraMultiplier.Construction.modulationCharacter, hunit, hunit]; norm_num

theorem boundedModulation_zero : boundedModulation ψ hψ hunit (0 : Local.FunctionsMetaplectic.Construction.Position F d) = 1 := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot 0 x) = 1
  simp [Local.FunctionsMetaplectic.Construction.dot]

theorem boundedModulation_add (p q : Local.FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (p + q) =
      boundedModulation ψ hψ hunit p * boundedModulation ψ hψ hunit q := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot (p + q) x) = ψ (Local.FunctionsMetaplectic.Construction.dot p x) * ψ (Local.FunctionsMetaplectic.Construction.dot q x)
  simp [Local.FunctionsMetaplectic.Construction.dot, add_mul, Finset.sum_add_distrib, ψ.map_add_eq_mul]

theorem boundedModulation_neg (p : Local.FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (-p) = star (boundedModulation ψ hψ hunit p) := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot (-p) x) = star (ψ (Local.FunctionsMetaplectic.Construction.dot p x))
  have hp : Local.FunctionsMetaplectic.Construction.dot (-p) x = -Local.FunctionsMetaplectic.Construction.dot p x := by simp [Local.FunctionsMetaplectic.Construction.dot]
  rw [hp, ψ.map_neg_eq_inv]
  exact Complex.inv_eq_conj (hunit _)

include hψ hunit in
theorem measures_eq_of_modulation_integrals
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hnontrivial : ∃ t, ψ t ≠ 1)
    (μ ν : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ p : Local.FunctionsMetaplectic.Construction.Position F d,
      ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x ∂μ = ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x ∂ν) : μ = ν := by
  exact CharacterMeasure.measures_eq_of_character_integrals
    (boundedModulation ψ hψ hunit) (boundedModulation_zero ψ hψ hunit)
    (boundedModulation_add ψ hψ hunit) (boundedModulation_neg ψ hψ hunit)
    (UltraMultiplier.Construction.modulationCharacter_separates ψ hnontrivial hunit) μ ν h

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ModulationMeasure.Construction
