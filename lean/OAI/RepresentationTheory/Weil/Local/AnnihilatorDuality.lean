import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier

/-! # Annihilator Duality -/

namespace OAI.RepresentationTheory.Weil.Local.AnnihilatorDuality.Construction

noncomputable section

/-! Double annihilators and the invariant product of compact-open subgroup volumes. -/

open _root_.MeasureTheory
open scoped Classical

theorem additiveAnnihilator_le_double
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ) (U : AddSubgroup (FunctionsMetaplectic.Construction.Position k n)) :
    U ≤ CompactCharacter.Construction.additiveAnnihilator ψ (CompactCharacter.Construction.additiveAnnihilator ψ U) := by
  intro x hx y hy
  rw [FourierTools.Construction.dot_comm]
  exact hy x hx

theorem fourier_square_indicator_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U V : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n))
    (hV : V.toAddSubgroup = CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup)
    (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ
      (FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)))) x =
      if x ∈ CompactCharacter.Construction.additiveAnnihilator ψ V.toAddSubgroup
      then (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) * (μ.real (V : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ)
      else 0 := by
  have hF : FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) =
      (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) •
        (V : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) := by
    funext y
    rw [CompactCharacter.Construction.fourier_indicator_subgroup, ← hV]
    by_cases hy : y ∈ V <;> simp [hy]
  rw [hF, FunctionsMetaplectic.Construction.fourierIntegral_smul]
  simp only [Pi.smul_apply, smul_eq_mul, CompactCharacter.Construction.fourier_indicator_subgroup]
  by_cases hx : x ∈ CompactCharacter.Construction.additiveAnnihilator ψ V.toAddSubgroup <;> simp [hx]

theorem nonarchimedean_annihilator_duality_and_scale
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n),
      IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) →
        CompactCharacter.Construction.additiveAnnihilator ψ (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup) = U.toAddSubgroup ∧
        μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) *
          μ.real (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) = c := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨c, hcpos, hsquare⟩ :=
    NonarchimedeanFourier.Construction.nonarchimedean_fourier_square_positive_scalar hNondiscrete n ψ hu hc hn μ
  refine ⟨c, hcpos, fun U hU => ?_⟩
  obtain ⟨_, hopen⟩ := CompactCharacter.Construction.additiveAnnihilator_compact_open hNondiscrete ψ hu hc hn μ U hU
  let V : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n) := ⟨CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, hopen⟩
  have hV : V.toAddSubgroup = CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup := rfl
  have h (x : FunctionsMetaplectic.Construction.Position k n) := hsquare
    ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)))
    (CompactCharacter.Construction.subgroup_indicator_locallyConstant U) (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU) x
  have hscale : (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) *
      (μ.real (V : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) = (c : ℂ) := by
    have h₀ := h 0
    rw [fourier_square_indicator_subgroup ψ μ U V hV] at h₀
    simpa using h₀
  constructor
  · apply le_antisymm
    · intro x hx
      have hxV : x ∈ CompactCharacter.Construction.additiveAnnihilator ψ V.toAddSubgroup := hx
      have hx' := h x
      rw [fourier_square_indicator_subgroup ψ μ U V hV, ite_eq_left hxV, hscale] at hx'
      by_contra hxU
      have hxneg : -x ∉ U := by
        intro hh
        apply hxU
        simpa only [neg_neg] using U.neg_mem hh
      simp only [Set.indicator_of_notMem hxneg, mul_zero] at hx'
      exact (Complex.ofReal_ne_zero.mpr hcpos.ne') hx'
    · exact additiveAnnihilator_le_double ψ U.toAddSubgroup
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    exact hscale

end

end OAI.RepresentationTheory.Weil.Local.AnnihilatorDuality.Construction
