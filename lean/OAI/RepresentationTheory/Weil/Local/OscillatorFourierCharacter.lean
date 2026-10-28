import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalFormProduct
import OAI.RepresentationTheory.Weil.Local.GeneralSchur
import OAI.RepresentationTheory.Weil.Local.BruhatCosets

/-! # Oscillator Fourier Character -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatorFourierCharacter.Construction

noncomputable section

section

/-! Scalar coordinates for actual oscillators on the Fourier cell. -/

open _root_.Matrix _root_.MeasureTheory

theorem nonarchimedean_testSpace_nontrivial
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    (hnd : ¬ DiscreteTopology k) (n : ℕ) : Nontrivial (FunctionsMetaplectic.Construction.schwartzBruhat k n) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  let b : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U (isCompact_closedBall 0 1))⟩
  refine ⟨⟨b, 0, ?_⟩⟩
  intro h
  have hv := congrArg (fun f : FunctionsMetaplectic.Construction.schwartzBruhat k n => f.val 0) h
  simp [b] at hv

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))

def oscillatorFourierNormalForm (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  QuadraticIntertwiner.Construction.quadraticOscillator ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) hu P *
    LinearIntertwiner.Construction.linearOscillator ψ B * w * QuadraticIntertwiner.Construction.quadraticOscillator ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) hu Q

theorem oscillatorFourierNormalForm_projection (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    OscillatorProjection.Construction.oscillatorProjection k n ψ (oscillatorFourierNormalForm ψ hu hc w P B Q) = FourierNormalForm.Construction.fourierNormalForm P B Q := by
  change Generators.Construction.quadraticSymplectic P * Generators.Construction.leviSymplectic B * w.val.1 * Generators.Construction.quadraticSymplectic Q = _
  change w.val.1 = Generators.Construction.weylSymplectic k n at hw
  rw [hw]
  rfl

theorem oscillatorFourierNormalForm_operator (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    (oscillatorFourierNormalForm ψ hu hc w P B Q).val.2 =
      TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) w.val.2 P.val B Q.val := rfl

def OscillatorFourierPresentation (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (z : ℂ) : Prop :=
  OscillatorProjection.Construction.oscillatorProjection k n ψ a = FourierNormalForm.Construction.fourierNormalForm P B Q ∧
    ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.2 f =
      z • TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F P.val B Q.val f

theorem exists_oscillatorFourierPresentation
    (hnd : ¬ DiscreteTopology k) (hn : ∃ t : k, ψ t ≠ 1)
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n) :
    ∃ (P Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (z : ℂˣ),
      OscillatorFourierPresentation ψ hu hc w.val.2 a P B Q z.val := by
  obtain ⟨P, Q, B, h⟩ := FourierNormalForm.Construction.exists_fourierNormalForm (OscillatorProjection.Construction.oscillatorProjection k n ψ a) ha
  have he : OscillatorProjection.Construction.oscillatorProjection k n ψ (oscillatorFourierNormalForm ψ hu hc w P B Q) =
      OscillatorProjection.Construction.oscillatorProjection k n ψ a := (oscillatorFourierNormalForm_projection ψ hu hc w hw P B Q).trans h.symm
  obtain ⟨z, hz, hscalar⟩ := BruhatCosets.Construction.nonarchimedean_oscillator_equal_projection hnd ψ hu hc hn
    (oscillatorFourierNormalForm ψ hu hc w P B Q) a he
  have hz0 : z ≠ 0 := by intro hz0; simp [hz0] at hz
  exact ⟨P, Q, B, Units.mk0 z hz0, h, hscalar⟩

omit [CharZero k] in
theorem oscillatorFourierPresentation_unique (hnd : ¬ DiscreteTopology k)
    (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n) (a : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (P P' Q Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n) (z z' : ℂ)
    (h : OscillatorFourierPresentation ψ hu hc F a P B Q z)
    (h' : OscillatorFourierPresentation ψ hu hc F a P' B' Q' z') :
    P = P' ∧ B = B' ∧ Q = Q' ∧ z = z' := by
  let : Nontrivial (FunctionsMetaplectic.Construction.schwartzBruhat k n) := nonarchimedean_testSpace_nontrivial hnd n
  obtain ⟨rfl, rfl, rfl⟩ := FourierNormalForm.Construction.fourierNormalForm_injective P P' Q Q' B B' (h.1.symm.trans h'.1)
  refine ⟨rfl, rfl, rfl, ?_⟩
  obtain ⟨f, hf⟩ := exists_ne (0 : FunctionsMetaplectic.Construction.schwartzBruhat k n)
  let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F P.val B Q.val
  have he := (h.2 (R.symm f)).symm.trans (h'.2 (R.symm f))
  change z • R (R.symm f) = z' • R (R.symm f) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact smul_left_injective ℂ hf he

end

section

/-! A well-defined determinant and scalar value on the oscillator Fourier cell. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k] {n : ℕ}
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

def nonarchimedeanFourierConstant : ℂˣ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn 1 ^ n

omit [CompleteSpace k] [SecondCountableTopology k] in
theorem nonarchimedeanFourierConstant_val :
    (nonarchimedeanFourierConstant (n := n) hnd ψ hu hc hn).val = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) := by
  change (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 2) ^ n = _
  rw [← pow_mul]

omit [CompleteSpace k] in
structure OscillatorFourierCoordinates (w a : FunctionsMetaplectic.Construction.Oscillator k n ψ) where
  P : FunctionsMetaplectic.Construction.SymmetricMatrix k n
  Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n
  B : FunctionsMetaplectic.Construction.GeneralLinear k n
  z : ℂˣ
  presentation : OscillatorFourierPresentation ψ hu hc w.val.2 a P B Q z.val

def oscillatorFourierCoordinates (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n) :
    OscillatorFourierCoordinates ψ hu hc w a := by
  have he : Nonempty (OscillatorFourierCoordinates ψ hu hc w a) := by
    obtain ⟨P, Q, B, z, h⟩ := exists_oscillatorFourierPresentation ψ hu hc hnd hn w hw a ha
    exact ⟨⟨P, Q, B, z, h⟩⟩
  exact Classical.choice he

def oscillatorFourierCharacterValue (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n) (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) : ℂˣ := by
  classical
  exact if ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n then
    let v := oscillatorFourierCoordinates hnd ψ hu hc hn w hw a ha
    v.z ^ 2 * GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k v.B) *
      nonarchimedeanFourierConstant (n := n) hnd ψ hu hc hn
  else 1

theorem oscillatorFourierCharacterValue_of_presentation
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (P Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (z : ℂˣ)
    (h : OscillatorFourierPresentation ψ hu hc w.val.2 a P B Q z.val) :
    oscillatorFourierCharacterValue hnd ψ hu hc hn hns w hw a =
      z ^ 2 * GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k B) *
        nonarchimedeanFourierConstant (n := n) hnd ψ hu hc hn := by
  have ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n := by
    rw [h.1]
    exact FourierNormalForm.Construction.fourierNormalForm_mem P B Q
  rw [oscillatorFourierCharacterValue, dite_eq_left ha]
  let v := oscillatorFourierCoordinates hnd ψ hu hc hn w hw a ha
  have he := oscillatorFourierPresentation_unique ψ hu hc hnd w.val.2 a v.P P v.Q Q v.B B v.z.val z.val
    v.presentation h
  have hz : v.z = z := Units.ext he.2.2.2
  change v.z ^ 2 * _ * _ = _
  rw [hz, he.2.1]

end

/-! Multiplicativity of the oscillator character on its Fourier coordinate domain. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k] {n : ℕ}
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem oscillatorFourierCharacterValue_mul
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hF : ∀ f x, (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x)
    (a b : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a ∈ FourierBigCell.Construction.fourierBigCell k n)
    (hb : OscillatorProjection.Construction.oscillatorProjection k n ψ b ∈ FourierBigCell.Construction.fourierBigCell k n)
    (hab : OscillatorProjection.Construction.oscillatorProjection k n ψ (a * b) ∈ FourierBigCell.Construction.fourierBigCell k n) :
    oscillatorFourierCharacterValue hnd ψ hu hc hn hns w hw (a * b) =
      oscillatorFourierCharacterValue hnd ψ hu hc hn hns w hw a *
        oscillatorFourierCharacterValue hnd ψ hu hc hn hns w hw b := by
  let A := oscillatorFourierCoordinates hnd ψ hu hc hn w hw a ha
  let D := oscillatorFourierCoordinates hnd ψ hu hc hn w hw b hb
  let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
  let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) w.val.2
  have hp : FourierNormalForm.Construction.fourierNormalForm A.P A.B A.Q * FourierNormalForm.Construction.fourierNormalForm D.P D.B D.Q ∈ FourierBigCell.Construction.fourierBigCell k n := by
    rw [← A.presentation.1, ← D.presentation.1, ← map_mul]
    exact hab
  obtain ⟨P, Q, B, Γ, hproj, hΓ, hR⟩ := NonarchimedeanNormalFormProduct.Construction.exists_nonarchimedean_normalForm_product hnd ψ hu hc hn hns
    w.val.2 hF A.P A.Q D.P D.Q A.B D.B hp
  have hg0 : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ≠ 0 :=
    FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn 1 one_ne_zero).2
  have hΓ0 : Γ ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide), zero_mul] at hΓ
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg0) (χ _).ne_zero) (χ _).ne_zero) hΓ.symm
  let z : ℂˣ := A.z * D.z * Units.mk0 Γ hΓ0
  have hpres : OscillatorFourierPresentation ψ hu hc w.val.2 (a * b) P B Q z.val := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, A.presentation.1, D.presentation.1, hproj]
    · intro f
      change a.val.2 (b.val.2 f) = (A.z.val * D.z.val * Γ) • R P.val B Q.val f
      rw [A.presentation.2, D.presentation.2, map_smul, hR, smul_smul, smul_smul]
  rw [oscillatorFourierCharacterValue_of_presentation hnd ψ hu hc hn hns w hw (a * b) P Q B z hpres,
    oscillatorFourierCharacterValue_of_presentation hnd ψ hu hc hn hns w hw a A.P A.Q A.B A.z A.presentation,
    oscillatorFourierCharacterValue_of_presentation hnd ψ hu hc hn hns w hw b D.P D.Q D.B D.z D.presentation]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, nonarchimedeanFourierConstant_val]
  change (A.z.val * D.z.val * Γ) ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k B)).val * FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) = _
  calc
    _ = A.z.val ^ 2 * D.z.val ^ 2 * (Γ ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k B)).val) *
        FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) := by ring
    _ = _ := by rw [hΓ]; ring

end

end OAI.RepresentationTheory.Weil.Local.OscillatorFourierCharacter.Construction
