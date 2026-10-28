import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep

/-! # Choice Open Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceOpenCover.Construction

noncomputable section

/-! A finite actual affine cover supplies canonical component-center choices from a finite differential-order bound. -/

universe u

variable (k : Type u) [CommRing k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.Smooth k R]

theorem exists_component_choice_neighborhood
    (J : Ideal R) (n : ℕ) (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤)
    (p : PrimeSpectrum R) :
    ∃ s ∉ p.asIdeal, Nonempty (CenterChoice.Construction.ComponentCenterChoice k (Localization.Away s)
      (J.map (algebraMap R (Localization.Away s))) n) := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hfirst : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k T = ⊤ :=
    (Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal k J n).trans hbound
  by_cases hT : T ≤ p.asIdeal
  · have hex : ∃ D : Derivation k R R, ∃ z : T, D z.val ∉ p.asIdeal := by
      by_contra h
      push Not at h
      have hle : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k T ≤ p.asIdeal := by
        apply sup_le hT
        apply Ideal.span_le.mpr
        rintro _ ⟨⟨D, z⟩, rfl⟩
        exact h D z
      rw [hfirst] at hle
      exact p.isPrime.ne_top (top_le_iff.mp hle)
    obtain ⟨D, z, hz⟩ := hex
    let S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z.val
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway (D z.val)
    have hz' : algebraMap R S z.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R S)) n := by
      rw [← Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J n]
      exact Ideal.mem_map_of_mem _ z.property
    exact ⟨D z.val, hz, ⟨.normal (algebraMap R S z.val) (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z.val)
      (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation D z.val) hz'⟩⟩
  · change ¬ ∀ x : R, x ∈ T → x ∈ p.asIdeal at hT
    push Not at hT
    obtain ⟨s, hs, hsp⟩ := hT
    let S := Localization.Away s
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway s
    have ht : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R S)) n = ⊤ := by
      rw [← Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J n]
      exact IdempotentQuotientCenter.Construction.center_map_away_member_eq_top T s hs
    exact ⟨s, hsp, ⟨.terminal ht⟩⟩

theorem exists_finite_component_choice_cover
    (J : Ideal R) (n : ℕ) (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    ∃ (p : Finset (PrimeSpectrum R)) (s : p → R),
      (⨆ i, PrimeSpectrum.basicOpen (s i)) = ⊤ ∧
      ∀ i, Nonempty (CenterChoice.Construction.ComponentCenterChoice k (Localization.Away (s i))
        (J.map (algebraMap R (Localization.Away (s i)))) n) := by
  classical
  choose s hs C using exists_component_choice_neighborhood k J n hbound
  have hcover : Set.univ ⊆ ⋃ p : PrimeSpectrum R, (PrimeSpectrum.basicOpen (s p) : Set (PrimeSpectrum R)) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hs p⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (s p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (s p)).isOpen) hcover
  refine ⟨t, fun p => s p.val, top_le_iff.mp ?_, fun p => C p.val⟩
  intro p _
  obtain ⟨q, hq, hp⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceOpenCover.Construction
