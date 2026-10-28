import OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization

/-! # Local Surjectivity -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalSurjectivity.Construction

noncomputable section

/-! Local oscillator lifts are obtained from the independently normalized
Schrödinger generators. No open-cell integral is used in this existence proof. -/

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

theorem localProjection_surjective_of_generators (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hQ : ∀ (B : Matrix (Fin N) (Fin N) k) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N),
      Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N) :
    Function.Surjective (Oscillator.Construction.localProjection k N ψ) := by
  let R := (Oscillator.Construction.localProjection k N ψ).range
  have hq (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) : Local.Generators.Construction.quadraticSymplectic B ∈ R :=
    ⟨NonarchimedeanIntertwiner.LocalAnalysis.quadraticOscillator ψ hQ hu B, rfl⟩
  have hw : SymplecticGeneration.weyl (k := k) (N := N) ∈ R := ⟨W, hW⟩
  have hm (A : Local.FunctionsMetaplectic.Construction.GeneralLinear k N) : SymplecticGeneration.levi A ∈ R :=
    ⟨NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A, rfl⟩
  have hup (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm) :
      SymplecticGeneration.upper B hB ∈ R := by
    have h := R.mul_mem (R.mul_mem (R.inv_mem hw) (hq ⟨-B, hB.neg⟩)) hw
    change SymplecticGeneration.weyl⁻¹ *
      SymplecticGeneration.lower (-B) hB.neg *
      SymplecticGeneration.weyl ∈ R at h
    rw [SymplecticGeneration.lower_conjugation] at h
    simpa only [neg_neg, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  have ht : R = ⊤ := SymplecticGeneration.subgroup_eq_top_of_generators R hup hm hw
  intro g
  have hg : g ∈ R := by rw [ht]; trivial
  exact hg

theorem localProjection_surjective_ultra [IsUltrametricDist k] [ProperSpace k]
    [NonarchimedeanAddGroup k]
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1) :
    Function.Surjective (Oscillator.Construction.localProjection k N ψ) :=
  localProjection_surjective_of_generators ψ hu
    (NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_quadratic_mem ψ hu hc)
    (NonarchimedeanNormalization.LocalAnalysis.nonarchimedeanRawFourierOscillator ψ hu hc hn N) rfl

theorem localProjection_surjective_real (ψ : AddChar ℝ ℂ)
    (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1) :
    Function.Surjective (Oscillator.Construction.localProjection ℝ N ψ) :=
  localProjection_surjective_of_generators ψ hu
    (fun B f => ArchimedeanCharacters.LocalAnalysis.quadraticOperator_archimedean_mem ψ (ArchimedeanCharacters.LocalAnalysis.real_character_temperate ψ hc hu) B f.property)
    (RealNormalization.LocalAnalysis.realRawFourierOscillator N ψ hc hu hn) rfl

theorem localProjection_surjective_complex (ψ : AddChar ℂ ℂ)
    (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1) :
    Function.Surjective (Oscillator.Construction.localProjection ℂ N ψ) :=
  localProjection_surjective_of_generators ψ hu
    (fun B f => ArchimedeanCharacters.LocalAnalysis.quadraticOperator_archimedean_mem ψ (ArchimedeanCharacters.LocalAnalysis.complex_character_temperate ψ hc hu) B f.property)
    (ComplexNormalization.LocalAnalysis.complexRawFourierOscillator N ψ hc hu hn) rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalSurjectivity.Construction
