import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence

/-! # Compact Character -/

namespace OAI.RepresentationTheory.Weil.Local.CompactCharacter.Construction

noncomputable section

section

/-! Compact locally constant Fourier analysis from small translations. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem character_finset_sum {k ι : Type*} [AddCommMonoid k]
    (ψ : AddChar k ℂ) (s : Finset ι) (a : ι → k) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, ψ.map_add_eq_mul, ih]

theorem compact_locallyConstant_translation
    {E : Type*} [NormedAddCommGroup E] {f : E → ℂ}
    (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x t : E, ‖t‖ < ε → f (x + t) = f x := by
  let : UniformSpace ℂ := ⊥
  have hu : UniformContinuous f := hs.uniformContinuous_of_continuous hf.continuous
  have h : {p : E × E | f p.1 = f p.2} ∈ uniformity E :=
    hu (DiscreteUniformity.relId_mem_uniformity ℂ)
  obtain ⟨ε, hε, heq⟩ := Metric.mem_uniformity_dist.mp h
  refine ⟨ε, hε, fun x t ht => heq (a := x + t) (b := x) ?_⟩
  simpa [dist_eq_norm] using ht

theorem fourierIntegral_translate
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun y => f (y + t)) x = ψ (FunctionsMetaplectic.Construction.dot x t) * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := μ)
    (fun y => ψ (FunctionsMetaplectic.Construction.dot x t) * (f y * ψ (-FunctionsMetaplectic.Construction.dot x y))) t
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hp : FunctionsMetaplectic.Construction.dot x (y + t) = FunctionsMetaplectic.Construction.dot x y + FunctionsMetaplectic.Construction.dot x t := by
      simp [FunctionsMetaplectic.Construction.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hp, neg_add, ψ.map_add_eq_mul]
    have hc : ψ (FunctionsMetaplectic.Construction.dot x t) * ψ (-FunctionsMetaplectic.Construction.dot x t) = 1 := by
      rw [← ψ.map_add_eq_mul]
      simp
    linear_combination -(f (y + t) * ψ (-FunctionsMetaplectic.Construction.dot x y)) * hc

theorem fourierIntegral_vanishes_of_translation
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : FunctionsMetaplectic.Construction.Position k n)
    (ht : ∀ y, f (y + t) = f y) (hx : ψ (FunctionsMetaplectic.Construction.dot x t) ≠ 1) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = 0 := by
  have h := fourierIntegral_translate ψ μ f t x
  have heq : (fun y => f (y + t)) = f := funext ht
  rw [heq] at h
  by_contra hn
  apply hx
  apply mul_right_cancel₀ hn
  simpa using h.symm

theorem fourierIntegral_compactSupport_of_locallyConstant
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hNontrivial : ∃ a : k, ψ a ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    HasCompactSupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨ε, hε, heq⟩ := compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hNontrivial
  have hR : 0 ≤ ‖a‖ / ε := div_nonneg (norm_nonneg _) hε.le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : FunctionsMetaplectic.Construction.Position k n) (‖a‖ / ε))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR hi)
  let t : FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : ‖t‖ < ε := by
    rw [show ‖t‖ = ‖a / x i‖ from Pi.norm_single _, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hxi)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hi
  have hdot : FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  have hzero := fourierIntegral_vanishes_of_translation ψ μ f t x
    (fun y => heq y t ht) (by rwa [hdot])
  exact hx hzero

theorem fourierIntegral_locallyConstant
    {k : Type} [NormedField k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hs : HasCompactSupport f) :
    IsLocallyConstant (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, hker⟩ := Metric.eventually_nhds_iff.mp (hψ.eventually_eq 0)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε / R, div_pos hε hR, fun y hy => ?_⟩
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : f z = 0
    · simp [hz]
    have hzR : ‖z‖ ≤ R := hbound z (subset_tsupport f hz)
    have hsmall : ‖y - x‖ * R < ε :=
      (lt_div_iff₀ hR).mp (by simpa [dist_eq_norm] using hy)
    have hchar : ψ (-FunctionsMetaplectic.Construction.dot (y - x) z) = 1 := by
      rw [FunctionsMetaplectic.Construction.dot, ← Finset.sum_neg_distrib, character_finset_sum]
      apply Finset.prod_eq_one
      intro i _
      have hnorm : ‖-((y - x) i * z i)‖ < ε := by
        rw [norm_neg, norm_mul]
        calc
          _ ≤ ‖y - x‖ * R := mul_le_mul
            (norm_le_pi_norm (y - x) i) ((norm_le_pi_norm z i).trans hzR)
            (norm_nonneg _) (norm_nonneg _)
          _ < ε := hsmall
      simpa only [ψ.map_zero_eq_one] using hker
        (show dist (-((y - x) i * z i)) 0 < ε by simpa using hnorm)
    have hsplit : -FunctionsMetaplectic.Construction.dot y z = -FunctionsMetaplectic.Construction.dot x z + -FunctionsMetaplectic.Construction.dot (y - x) z := by
      simp only [FunctionsMetaplectic.Construction.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hsplit, ψ.map_add_eq_mul, hchar, mul_one]

/-- The Fourier integral preserves the actual nonarchimedean Bruhat space. -/
theorem nonarchimedean_fourier_mem
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) (hNontrivial : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  exact FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    (fourierIntegral_locallyConstant ψ
      (NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hUnitary hContinuous) μ hs)
    (fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hNontrivial μ hf hs)

end

/-! Character orthogonality on additive subgroups for local Fourier inversion. -/

open _root_.MeasureTheory
open scoped Classical

theorem integral_character_subgroup
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (U : OpenAddSubgroup E)
    (χ : AddChar E ℂ) :
    (∫ x in (U : Set E), χ x ∂μ) =
      if ∀ x ∈ U, χ x = 1 then (μ.real (U : Set E) : ℂ) else 0 := by
  by_cases hχ : ∀ x ∈ U, χ x = 1
  · rw [ite_eq_left hχ]
    calc
      _ = ∫ _ in (U : Set E), (1 : ℂ) ∂μ :=
        setIntegral_congr_fun U.isOpen.measurableSet (fun x hx => hχ x hx)
      _ = _ := by simp
  · rw [ite_eq_right hχ]
    push Not at hχ
    obtain ⟨a, ha, hχa⟩ := hχ
    let f : E → ℂ := (U : Set E).indicator (fun x => χ x)
    have hfun : (fun x => f (x + a)) = fun x => χ a * f x := by
      funext x
      have hmem : x + a ∈ U ↔ x ∈ U := U.add_mem_cancel_right ha
      by_cases hx : x ∈ U
      · simp [f, hx, hmem.mpr hx, χ.map_add_eq_mul, mul_comm]
      · simp [f, hx, show x + a ∉ U from fun h => hx (hmem.mp h)]
    have h := integral_add_right_eq_self (μ := μ) f a
    rw [hfun, integral_const_mul] at h
    have hf : (∫ x, f x ∂μ) = 0 := by
      by_contra hne
      apply hχa
      apply mul_right_cancel₀ hne
      simpa using h
    simpa only [f, integral_indicator U.isOpen.measurableSet] using hf

def additiveAnnihilator
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ) (U : AddSubgroup (FunctionsMetaplectic.Construction.Position k n)) :
    AddSubgroup (FunctionsMetaplectic.Construction.Position k n) where
  carrier := {x | ∀ y ∈ U, ψ (FunctionsMetaplectic.Construction.dot x y) = 1}
  zero_mem' := by simp [FunctionsMetaplectic.Construction.dot]
  add_mem' {x z} hx hz y hy := by
    have hdot : FunctionsMetaplectic.Construction.dot (x + z) y = FunctionsMetaplectic.Construction.dot x y + FunctionsMetaplectic.Construction.dot z y := by
      simp [FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hdot, ψ.map_add_eq_mul, hx y hy, hz y hy, one_mul]
  neg_mem' {x} hx y hy := by
    have hdot : FunctionsMetaplectic.Construction.dot (-x) y = -FunctionsMetaplectic.Construction.dot x y := by simp [FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
    rw [hdot, ψ.map_neg_eq_inv, hx y hy, inv_one]

theorem integral_pairing_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (x : FunctionsMetaplectic.Construction.Position k n) :
    (∫ y in (U : Set (FunctionsMetaplectic.Construction.Position k n)), ψ (FunctionsMetaplectic.Construction.dot x y) ∂μ) =
      if x ∈ additiveAnnihilator ψ U.toAddSubgroup then (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 := by
  let χ : AddChar (FunctionsMetaplectic.Construction.Position k n) ℂ :=
    ψ.compAddMonoidHom (dotProductBilin k k x).toAddMonoidHom
  exact integral_character_subgroup μ U χ

theorem fourier_indicator_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) x =
      if x ∈ additiveAnnihilator ψ U.toAddSubgroup then (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  have heq : (fun y => (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) y * ψ (-FunctionsMetaplectic.Construction.dot x y)) =
      (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun y => ψ (FunctionsMetaplectic.Construction.dot (-x) y)) := by
    funext y
    by_cases hy : y ∈ U <;> simp [hy, FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
  rw [heq, integral_indicator U.isOpen.measurableSet, integral_pairing_subgroup]
  simp only [neg_mem_iff]

theorem subgroup_indicator_locallyConstant
    {E : Type*} [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (U : OpenAddSubgroup E) :
    IsLocallyConstant ((U : Set E).indicator (fun _ => (1 : ℂ))) := by
  have h := (LocallyConstant.charFn ℂ
    (show IsClopen (U : Set E) from ⟨U.isClosed, U.isOpen⟩)).isLocallyConstant
  change IsLocallyConstant ((U : Set E).indicator (1 : E → ℂ)) at h
  convert! h using 1

theorem subgroup_indicator_compactSupport
    {E : Type*} [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] [T2Space E]
    (U : OpenAddSubgroup E) (hU : IsCompact (U : Set E)) :
    HasCompactSupport ((U : Set E).indicator (fun _ => (1 : ℂ))) := by
  apply HasCompactSupport.intro hU
  intro x hx
  simp [hx]

theorem additiveAnnihilator_compact_open
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n))) :
    IsCompact (additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) ∧
      IsOpen (additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let f : FunctionsMetaplectic.Construction.Position k n → ℂ := (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))
  have hf := subgroup_indicator_compactSupport U hU
  have hF := fourierIntegral_locallyConstant ψ
    (NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc) μ hf
  have hμ : (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (ENNReal.toReal_pos _ hU.measure_ne_top).ne'
    exact (Measure.measure_pos_of_nonempty_interior μ
      (by rw [U.isOpen.interior_eq]; exact ⟨0, U.zero_mem⟩)).ne'
  have hann : (additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) =
      {x | FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ)} := by
    ext x
    change x ∈ additiveAnnihilator ψ U.toAddSubgroup ↔
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) x = _
    rw [fourier_indicator_subgroup]
    by_cases hx : x ∈ additiveAnnihilator ψ U.toAddSubgroup <;> simp [hx, hμ.symm]
  have hclosed : IsClosed (additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) := by
    rw [hann]
    exact hF.isClosed_fiber _
  have hcompact := fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μ
    (subgroup_indicator_locallyConstant U) hf
  constructor
  · apply hcompact.of_isClosed_subset hclosed
    intro x hx
    apply subset_tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)
    have hx' := congrArg (fun S : Set (FunctionsMetaplectic.Construction.Position k n) => x ∈ S) hann
    have heq : FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) := by
      exact (Eq.mp hx' hx)
    change FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x ≠ 0
    rwa [heq]
  · rw [hann]
    exact hF.isOpen_fiber _

end

end OAI.RepresentationTheory.Weil.Local.CompactCharacter.Construction
