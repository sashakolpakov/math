import OAI.RepresentationTheory.Weil.Local.Coordinates
import OAI.RepresentationTheory.Weil.Local.RealCharacters
import OAI.RepresentationTheory.Weil.Local.OscillatorSchur

/-! # General Schur -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralSchur.Construction

noncomputable section

/-! The oscillator kernel is scalar over every natural local field allowed in LocalWeil. -/

def dotCharacter {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (p : FunctionsMetaplectic.Construction.Position k n) : AddChar (FunctionsMetaplectic.Construction.Position k n) ℂ where
  toFun x := ψ (FunctionsMetaplectic.Construction.dot p x)
  map_zero_eq_one' := by simp [FunctionsMetaplectic.Construction.dot]
  map_add_eq_mul' x y := by simp [FunctionsMetaplectic.Construction.dot, mul_add, Finset.sum_add_distrib, ψ.map_add_eq_mul]

theorem modulation_mem
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k] {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (p : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (fun x => ψ (FunctionsMetaplectic.Construction.dot p x) * f.val x) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  by_cases h : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k := IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
    exact FunctionsMetaplectic.Construction.compact_locallyConstant_mem
      (((NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc).comp_continuous
        (by unfold FunctionsMetaplectic.Construction.dot; fun_prop)).mul hf) hs.mul_left
  · obtain ⟨r, ⟨e⟩⟩ := Coordinates.Construction.exists_real_coordinates_of_unbounded k h n
    apply RealCharacters.Construction.realChart_character_mul_mem e (dotCharacter ψ p) _ (fun x => hu _) f.property
    exact hc.comp (by unfold FunctionsMetaplectic.Construction.dot; fun_prop)

theorem oscillator_kernel_scalar
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.2 f = z • f := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  exact OscillatorSchur.Construction.oscillator_kernel_scalar_of_modulation_stability ψ hc hu hn (modulation_mem ψ hc hu) a ha

theorem oscillator_same_projection_unit_scalar
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a b : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hab : OscillatorProjection.Construction.oscillatorProjection k n ψ a = OscillatorProjection.Construction.oscillatorProjection k n ψ b) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.2 f = z • b.val.2 f := by
  have hker : OscillatorProjection.Construction.oscillatorProjection k n ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨z, hz, h⟩ := oscillator_kernel_scalar hNondiscrete ψ hc hu hn (a * b⁻¹) hker
  refine ⟨z, hz, fun f => ?_⟩
  have hh := h (b.val.2 f)
  change a.val.2 (b.val.2.symm (b.val.2 f)) = z • b.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using hh

theorem oscillator_kernel_central
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a = 1)
    (b : FunctionsMetaplectic.Construction.Oscillator k n ψ) : a * b = b * a := by
  obtain ⟨z, _, hz⟩ := oscillator_kernel_scalar hNondiscrete ψ hc hu hn a ha
  apply Subtype.ext
  apply Prod.ext
  · change a.val.1 * b.val.1 = b.val.1 * a.val.1
    have hp : a.val.1 = 1 := ha
    rw [hp, one_mul, mul_one]
  · apply LinearEquiv.ext
    intro f
    change a.val.2 (b.val.2 f) = b.val.2 (a.val.2 f)
    rw [hz, hz, map_smul]

end

end OAI.RepresentationTheory.Weil.Local.GeneralSchur.Construction
