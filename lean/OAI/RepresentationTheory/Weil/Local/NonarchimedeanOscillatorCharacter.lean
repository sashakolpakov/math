import OAI.RepresentationTheory.Weil.Local.OscillatorFourierCharacter
import OAI.RepresentationTheory.Weil.Local.CharacterExtension

/-! # Nonarchimedean Oscillator Character -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanOscillatorCharacter.Construction

noncomputable section

/-! A character of the actual oscillator group whose scalar restriction is the square. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

include hnd hu hc hn hns in
theorem exists_nonarchimedean_oscillator_character (n : ℕ) :
    ∃ Θ : FunctionsMetaplectic.Construction.Oscillator k n ψ →* ℂˣ,
      ∀ (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (z : ℂˣ),
        OscillatorProjection.Construction.oscillatorProjection k n ψ a = 1 →
        (∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.2 f = z.val • f) → Θ a = z ^ 2 := by
  classical
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  obtain ⟨w, hw, hF⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_normalized_fourier_oscillator hnd n ψ hu hc hn
  let Ω : Set (FunctionsMetaplectic.Construction.Oscillator k n ψ) := {a | OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n}
  let c := OscillatorFourierCharacter.Construction.oscillatorFourierCharacterValue hnd ψ hu hc hn hns w hw
  have hrich : ∀ E : Finset (FunctionsMetaplectic.Construction.Oscillator k n ψ), ∃ x, ∀ g ∈ E, x * g ∈ Ω :=
    FourierBigCell.Construction.oscillator_fourierBigCell_finite_left_translates hnd n ψ hu hc hn
  have hmul : ∀ a b, a ∈ Ω → b ∈ Ω → a * b ∈ Ω → c (a * b) = c a * c b :=
    OscillatorFourierCharacter.Construction.oscillatorFourierCharacterValue_mul hnd ψ hu hc hn hns w hw hF
  obtain ⟨Θ, hΘ⟩ := CharacterExtension.Construction.exists_group_character_extension Ω c hrich hmul
  refine ⟨Θ, ?_⟩
  intro a z ha hz
  obtain ⟨b, hb⟩ := hrich {1}
  have hbΩ : b ∈ Ω := by simpa only [mul_one] using hb 1 (by simp)
  have hba : b * a ∈ Ω := by
    change OscillatorProjection.Construction.oscillatorProjection k n ψ (b * a) ∈ FourierBigCell.Construction.fourierBigCell k n
    rw [map_mul, ha, mul_one]
    exact hbΩ
  let D := OscillatorFourierCharacter.Construction.oscillatorFourierCoordinates hnd ψ hu hc hn w hw b hbΩ
  let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
  let g := OscillatorFourierCharacter.Construction.nonarchimedeanFourierConstant (n := n) hnd ψ hu hc hn
  have hpres : OscillatorFourierCharacter.Construction.OscillatorFourierPresentation ψ hu hc w.val.2 (b * a) D.P D.B D.Q (D.z * z).val := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, ha, mul_one]
      exact D.presentation.1
    · intro f
      change b.val.2 (a.val.2 f) = (D.z.val * z.val) • _
      rw [hz, map_smul, D.presentation.2, smul_smul, mul_comm z.val]
  have hbval : Θ b = D.z ^ 2 * χ (FunctionsMetaplectic.Construction.determinantUnit k D.B) * g := by
    rw [hΘ b hbΩ]
    exact OscillatorFourierCharacter.Construction.oscillatorFourierCharacterValue_of_presentation hnd ψ hu hc hn hns w hw b D.P D.Q D.B D.z D.presentation
  have hbaval : Θ (b * a) = (D.z * z) ^ 2 * χ (FunctionsMetaplectic.Construction.determinantUnit k D.B) * g := by
    rw [hΘ (b * a) hba]
    exact OscillatorFourierCharacter.Construction.oscillatorFourierCharacterValue_of_presentation hnd ψ hu hc hn hns w hw (b * a)
      D.P D.Q D.B (D.z * z) hpres
  apply mul_left_cancel (a := Θ b)
  rw [← map_mul, hbaval, hbval, mul_pow]
  ac_rfl

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanOscillatorCharacter.Construction
