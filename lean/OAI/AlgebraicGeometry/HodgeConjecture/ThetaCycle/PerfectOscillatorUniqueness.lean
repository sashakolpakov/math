import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPerfect
import OAI.RepresentationTheory.Theta.Adelic.ArchComparison

/-! # Perfect Oscillator Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PerfectOscillatorUniqueness.CM

noncomputable section

/-! Uniqueness of actual oscillator lifts of a perfect group, using the
proved Heisenberg commutant theorem and its scalar comparison character. -/

open OAI.RepresentationTheory.Theta.Adelic.BallNatural

theorem perfect_oscillator_lifts_agree
    {G : Type*} [Group G] (hG : commutator G = ⊤)
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hk : ¬ DiscreteTopology k)
    (hn : ∃ x : k, ψ x ≠ 1) {N : ℕ}
    (s t : G →* RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : ∀ g, RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (s g) = RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (t g)) : s = t := by
  obtain ⟨f₀, hf₀⟩ := RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  obtain ⟨χ, hχ⟩ := RepresentationTheory.Theta.Adelic.SplitComparison.scalar_difference_character
    ((RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp s) ((RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp t) f₀ hf₀
    (fun g => RepresentationTheory.Theta.Adelic.ArchComparison.same_projection_scalar ψ hc hu hk hn
      (s g) (t g) (hp g))
  have hz (g : G) : χ g = 1 := by
    apply Abelianization.commutator_subset_ker χ
    rw [hG]
    trivial
  apply DFunLike.ext
  intro g
  apply RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi.Construction.localCover_ext (hp g)
  intro f x
  have he := hχ g f
  simp only [MonoidHom.comp_apply, hz g, Circle.coe_one, one_smul] at he
  exact congrArg (fun q : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N => q.val x) he

theorem ball_oscillator_lifts_agree
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hk : ¬ DiscreteTopology k)
    (hn : ∃ x : k, ψ x ≠ 1) {N : ℕ}
    (s t : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup →* RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : ∀ g, RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (s g) = RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (t g)) : s = t :=
  perfect_oscillator_lifts_agree BallPerfect.CM.ball_group_commutator_eq_top ψ hc hu hk hn s t hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PerfectOscillatorUniqueness.CM
