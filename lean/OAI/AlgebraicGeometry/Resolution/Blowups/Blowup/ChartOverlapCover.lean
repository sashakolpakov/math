import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlap
import Mathlib.RingTheory.Ideal.Span

/-! # Chart Overlap Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlapCover.Construction

noncomputable section

/-! Every finite center frame supplies a common open refinement of any blowup chart. -/

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Ratios of any finite generating family generate the unit ideal on every chart. -/
theorem blowupChartRatio_span_top {ι : Type u} [Fintype ι]
    (g : ι → I) (hgen : Ideal.span (Set.range (fun j => (g j).val)) = I) (a : I) :
    Ideal.span (Set.range (fun j => ExceptionalIdeal.Construction.blowupChartRatio I a (g j))) = ⊤ := by
  have ha : a.val ∈ Ideal.span (Set.range (fun j => (g j).val)) := by
    rw [hgen]
    exact a.property
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hone : ∑ j, Charts.Construction.blowupChartConstants I a (c j) * ExceptionalIdeal.Construction.blowupChartRatio I a (g j) = 1 := by
    apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
    calc
      Charts.Construction.blowupChartConstants I a a.val *
          (∑ j, Charts.Construction.blowupChartConstants I a (c j) * ExceptionalIdeal.Construction.blowupChartRatio I a (g j)) =
          ∑ j, Charts.Construction.blowupChartConstants I a (c j) *
            (Charts.Construction.blowupChartConstants I a a.val * ExceptionalIdeal.Construction.blowupChartRatio I a (g j)) := by
        exact (Finset.mul_sum Finset.univ
          (fun j => Charts.Construction.blowupChartConstants I a (c j) * ExceptionalIdeal.Construction.blowupChartRatio I a (g j))
          (Charts.Construction.blowupChartConstants I a a.val)).trans
            (Finset.sum_congr rfl (fun j _ => by ring))
      _ = ∑ j, Charts.Construction.blowupChartConstants I a (c j * (g j).val) := by
        simp only [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, map_mul]
      _ = Charts.Construction.blowupChartConstants I a a.val * 1 := by
        rw [← map_sum, hc, mul_one (Charts.Construction.blowupChartConstants I a a.val)]
  rw [Ideal.eq_top_iff_one, ← hone]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- A point where `b/a` is invertible lifts to the actual homogeneous overlap. -/
theorem exists_blowupChartOverlap_prime (a b : I) (p : PrimeSpectrum (Charts.Construction.blowupChart I a))
    (hb : ExceptionalIdeal.Construction.blowupChartRatio I a b ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (ChartOverlap.Construction.blowupChartOverlap I a b),
      PrimeSpectrum.comap (ChartOverlap.Construction.blowupChartOverlapLeft I a b) q = p := by
  let := (ChartOverlap.Construction.blowupChartOverlapLeft I a b).toAlgebra
  let := ChartOverlap.Construction.blowupChartOverlapLeft_isLocalization I a b
  have hdis : Disjoint (Submonoid.powers (ExceptionalIdeal.Construction.blowupChartRatio I a b) : Set (Charts.Construction.blowupChart I a))
      p.asIdeal := (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hb
  have hQ := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (ExceptionalIdeal.Construction.blowupChartRatio I a b)) (ChartOverlap.Construction.blowupChartOverlap I a b)
    p.asIdeal inferInstance hdis
  refine ⟨⟨p.asIdeal.map (ChartOverlap.Construction.blowupChartOverlapLeft I a b), hQ⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers (ExceptionalIdeal.Construction.blowupChartRatio I a b)) (ChartOverlap.Construction.blowupChartOverlap I a b)
    inferInstance hdis

/-- Replacing the finite generating family loses no points: the actual
overlaps with the replacement charts jointly cover each original chart. -/
theorem blowupChartOverlap_family_covers {ι : Type u} [Fintype ι]
    (g : ι → I) (hgen : Ideal.span (Set.range (fun j => (g j).val)) = I)
    (a : I) (p : PrimeSpectrum (Charts.Construction.blowupChart I a)) :
    ∃ j, ∃ q : PrimeSpectrum (ChartOverlap.Construction.blowupChartOverlap I a (g j)),
      PrimeSpectrum.comap (ChartOverlap.Construction.blowupChartOverlapLeft I a (g j)) q = p := by
  have hex : ∃ j, ExceptionalIdeal.Construction.blowupChartRatio I a (g j) ∉ p.asIdeal := by
    by_contra! h
    have hle : Ideal.span (Set.range (fun j => ExceptionalIdeal.Construction.blowupChartRatio I a (g j))) ≤ p.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact h j
    rw [blowupChartRatio_span_top I g hgen a] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨j, hj⟩ := hex
  obtain ⟨q, hq⟩ := exists_blowupChartOverlap_prime I a (g j) p hj
  exact ⟨j, q, hq⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlapCover.Construction
