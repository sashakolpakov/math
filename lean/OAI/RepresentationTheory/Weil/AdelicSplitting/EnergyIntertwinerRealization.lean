import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalSurjectivity
import OAI.RepresentationTheory.Weil.UnitarySplitting.EnergyIntertwinerNormalization

/-! # Energy Intertwiner Realization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.EnergyIntertwinerRealization.Construction

noncomputable section

/-! An actual energy-preserving Bruhat intertwiner is an oscillator lift
when an independent lift of the same symplectic element is available. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.EnergyIntertwinerNormalization.Construction

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

theorem energy_intertwiner_local_realization
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ)
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N)
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (henergy : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy k N (A f) = Local.FunctionsMetaplectic.Construction.l2Energy k N f)
    (hcov : ∀ v f, A (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
      UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (A f))
    (a : Oscillator.Construction.LocalCover k N ψ) (ha : Oscillator.Construction.localProjection k N ψ a = g) :
    ∃ U : Oscillator.Construction.LocalCover k N ψ, Oscillator.Construction.localProjection k N ψ U = g ∧ ∀ f, Oscillator.Construction.localOperator k N ψ U f = A f := by
  have hacov (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      a.val.2 (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
        UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (a.val.2 f) := by
    apply Subtype.ext
    have hh := (a.property.2 v f (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).mp rfl
    change (a.val.2 (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).val =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction (Oscillator.Construction.localProjection k N ψ a) v) (a.val.2 f).val at hh
    rwa [ha] at hh
  obtain ⟨r, V, hr, hA, hV, hVc⟩ := UnitarySplitting.EnergyIntertwinerNormalization.Construction.energyIntertwiner_positive_normalization hk ψ hc hu hn
    (Local.FunctionsMetaplectic.Construction.symplecticAction g) A hcov 1 zero_lt_one (by simpa only [one_mul] using henergy)
    a.val.2 hacov a.property.1
  obtain ⟨u, hu0⟩ := UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  have huE : Local.FunctionsMetaplectic.Construction.l2Energy k N u ≠ 0 := fun he => hu0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N u).mp he)
  have he := henergy u
  rw [hA, UnitarySplitting.FourierPairing.Construction.l2Energy_smul, hV, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at he
  have hr2 : r ^ 2 = 1 := mul_right_cancel₀ huE (he.trans (one_mul _).symm)
  have hr1 : r = 1 := by nlinarith
  have hAV (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : A f = V f := by simpa only [hr1, Complex.ofReal_one, one_smul] using hA f
  let U : Oscillator.Construction.LocalCover k N ψ := ⟨(g, V), ⟨hV, by
    intro v f h
    constructor
    · intro hh
      have hh' : h = UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f := Subtype.ext hh
      rw [hh']
      exact congrArg Subtype.val (hVc v f)
    · intro hh
      have hh' : V h = UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (V f) := Subtype.ext hh
      rw [← hVc] at hh'
      exact congrArg Subtype.val (V.injective hh')⟩⟩
  exact ⟨U, rfl, fun f => (hAV f).symm⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.EnergyIntertwinerRealization.Construction
