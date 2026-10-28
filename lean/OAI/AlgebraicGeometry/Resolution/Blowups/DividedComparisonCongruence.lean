import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartGeneratorComparison
import Mathlib.Tactic.Ring

/-! # Divided Comparison Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DividedComparisonCongruence.Construction

noncomputable section

/-! Comparison maps remain congruent on blowup ratios after their coefficient differences are divided by the exceptional parameter. -/

universe u v

theorem blowupChart_congruence_of_divided_constants
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] (I : Ideal R) (a : I)
    (f g : Blowup.Charts.Construction.blowupChart I a →+* S) (T : Ideal S)
    (hregular : IsRegular (f (Blowup.Charts.Construction.blowupChartConstants I a a.val)))
    (u : Sˣ) (hu : g (Blowup.Charts.Construction.blowupChartConstants I a a.val) = f (Blowup.Charts.Construction.blowupChartConstants I a a.val) * u)
    (hdiff : ∀ r : R, ∃ d ∈ T,
      g (Blowup.Charts.Construction.blowupChartConstants I a r) - f (Blowup.Charts.Construction.blowupChartConstants I a r) = f (Blowup.Charts.Construction.blowupChartConstants I a a.val) * d) :
    ∀ x : Blowup.Charts.Construction.blowupChart I a, g x - f x ∈ T := by
  let α := f (Blowup.Charts.Construction.blowupChartConstants I a a.val)
  have huT : (u : S) - 1 ∈ T := by
    obtain ⟨d, hd, he⟩ := hdiff a.val
    have he' : (u : S) - 1 = d := by
      apply hregular.left
      change α * ((u : S) - 1) = α * d
      calc
        _ = g (Blowup.Charts.Construction.blowupChartConstants I a a.val) - f (Blowup.Charts.Construction.blowupChartConstants I a a.val) := by rw [hu]; dsimp [α]; ring
        _ = _ := he
    exact he' ▸ hd
  have hratios (b : I) : g (ExceptionalIdeal.Construction.blowupChartRatio I a b) - f (ExceptionalIdeal.Construction.blowupChartRatio I a b) ∈ T := by
    obtain ⟨d, hd, he⟩ := hdiff b.val
    have hf := congrArg f (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a b)
    have hg := congrArg g (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a b)
    simp only [map_mul] at hf hg
    have hv : (u : S) * g (ExceptionalIdeal.Construction.blowupChartRatio I a b) - f (ExceptionalIdeal.Construction.blowupChartRatio I a b) = d := by
      apply hregular.left
      change α * ((u : S) * g (ExceptionalIdeal.Construction.blowupChartRatio I a b) - f (ExceptionalIdeal.Construction.blowupChartRatio I a b)) = α * d
      calc
        _ = g (Blowup.Charts.Construction.blowupChartConstants I a a.val) * g (ExceptionalIdeal.Construction.blowupChartRatio I a b) -
            f (Blowup.Charts.Construction.blowupChartConstants I a a.val) * f (ExceptionalIdeal.Construction.blowupChartRatio I a b) := by rw [hu]; dsimp [α]; ring
        _ = _ := by rw [hf, hg, he]
    have hm : (u : S) * (g (ExceptionalIdeal.Construction.blowupChartRatio I a b) - f (ExceptionalIdeal.Construction.blowupChartRatio I a b)) ∈ T := by
      have he' : (u : S) * (g (ExceptionalIdeal.Construction.blowupChartRatio I a b) - f (ExceptionalIdeal.Construction.blowupChartRatio I a b)) =
          d - ((u : S) - 1) * f (ExceptionalIdeal.Construction.blowupChartRatio I a b) := by rw [← hv]; ring
      rw [he']
      exact T.sub_mem hd (T.mul_mem_right _ huT)
    exact (Ideal.unit_mul_mem_iff_mem T u.isUnit).mp hm
  let Q := Ideal.Quotient.mk T
  have hq : Q.comp g = Q.comp f := by
    apply Blowup.ChartGeneratorComparison.Construction.blowupChart_hom_ext_of_constants_ratios I a
    · intro r
      apply Ideal.Quotient.eq.mpr
      obtain ⟨d, hd, he⟩ := hdiff r
      rw [he]
      exact T.mul_mem_left _ hd
    · intro b
      exact Ideal.Quotient.eq.mpr (hratios b)
  intro x
  exact Ideal.Quotient.eq.mp (RingHom.congr_fun hq x)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DividedComparisonCongruence.Construction
