import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Fiber Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.FiberMeasure.Construction

noncomputable section

section

/-! Finite measurable fiber enumerations lift invariant probability
measures by summing over the fibers and normalizing. -/

open scoped Classical ENNReal
open _root_.MeasureTheory

theorem sum_map_eq_of_pointwise_permutation
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    (μ : Measure Y) (f g : ι → Y → X) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hperm : ∀ y, ∃ e : ι ≃ ι, ∀ i, f i y = g (e i) y) :
    (∑ i, μ.map (f i)) = ∑ i, μ.map (g i) := by
  apply Measure.ext
  intro s hs
  simp only [Measure.finsetSum_apply, Measure.map_apply, hf, hg, hs]
  have hfi (i : ι) : Measurable ((f i ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hs.preimage (hf i))
  have hgi (i : ι) : Measurable ((g i ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hs.preimage (hg i))
  have hfint (i : ι) : μ (f i ⁻¹' s) =
      ∫⁻ y, (f i ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ :=
    (lintegral_indicator_one (hs.preimage (hf i))).symm
  have hgint (i : ι) : μ (g i ⁻¹' s) =
      ∫⁻ y, (g i ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ :=
    (lintegral_indicator_one (hs.preimage (hg i))).symm
  simp only [hfint, hgint]
  rw [← lintegral_finsetSum _ (fun i _ => hfi i), ← lintegral_finsetSum _ (fun i _ => hgi i)]
  apply lintegral_congr
  intro y
  obtain ⟨e, he⟩ := hperm y
  calc
    _ = ∑ i, (g (e i) ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Set.indicator_apply, Set.mem_preimage, he i]
    _ = _ := Equiv.sum_comp e (fun i => (g i ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y)

theorem invariant_probability_of_finite_enumeration
    {H X Y ι : Type*} [Group H] [MulAction H X] [MulAction H Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableConstSMul H X] [MeasurableConstSMul H Y]
    [Fintype ι] [Nonempty ι] (μ : Measure Y) [IsProbabilityMeasure μ] [SMulInvariantMeasure H Y μ]
    (f : ι → Y → X) (hf : ∀ i, Measurable (f i))
    (hperm : ∀ (h : H) (y : Y), ∃ e : ι ≃ ι, ∀ i, h • f i y = f (e i) (h • y)) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ SMulInvariantMeasure H X ν := by
  let ν : Measure X := ∑ i, μ.map (f i)
  have hmass : ν Set.univ = Fintype.card ι := by
    simp only [ν, Measure.finsetSum_apply, Measure.map_apply (hf _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  let : SMulInvariantMeasure H X ν := by
    constructor
    intro h s hs
    have he := sum_map_eq_of_pointwise_permutation μ
      (fun i y => h • f i y) (fun i y => f i (h • y))
      (fun i => (measurable_const_smul h).comp (hf i))
      (fun i => (hf i).comp (measurable_const_smul h)) (hperm h)
    have heval := congrArg (fun η : Measure X => η s) he
    have hl (i : ι) : (μ.map (fun y => h • f i y)) s = μ ((fun y => h • f i y) ⁻¹' s) :=
      Measure.map_apply ((measurable_const_smul h).comp (hf i)) hs
    have hr (i : ι) : (μ.map (fun y => f i (h • y))) s = μ ((fun y => f i (h • y)) ⁻¹' s) :=
      Measure.map_apply ((hf i).comp (measurable_const_smul h)) hs
    simp only [Measure.finsetSum_apply, hl, hr] at heval
    change (∑ i, μ (f i ⁻¹' ((h • ·) ⁻¹' s))) =
      ∑ i, μ ((h • ·) ⁻¹' (f i ⁻¹' s)) at heval
    change (∑ i, μ.map (f i)) ((h • ·) ⁻¹' s) = (∑ i, μ.map (f i)) s
    simp only [Measure.finsetSum_apply,
      Measure.map_apply (hf _) (hs.preimage (measurable_const_smul h)), Measure.map_apply (hf _) hs]
    rw [heval]
    apply Finset.sum_congr rfl
    intro i _
    exact SMulInvariantMeasure.measure_preimage_smul h (hs.preimage (hf i))
  apply QuotientMeasure.Construction.invariant_probability_of_finite (H := H) ν
  · rw [hmass]
    exact_mod_cast Fintype.card_ne_zero
  · rw [hmass]
    exact ENNReal.natCast_ne_top _

end

/-! An equivariant projection with a finite product parametrization
permutes each fiber under the group action. -/

open scoped Classical

theorem finite_product_fiber_permutation
    {H X Y ι : Type*} [Group H] [MulAction H X] [MulAction H Y] [Finite ι]
    (e : X ≃ Y × ι) (he : ∀ (h : H) x, (e (h • x)).1 = h • (e x).1)
    (h : H) (y : Y) :
    ∃ p : ι ≃ ι, ∀ i, h • e.symm (y, i) = e.symm (h • y, p i) := by
  let f : ι → ι := fun i => (e (h • e.symm (y, i))).2
  have hfst (i : ι) : (e (h • e.symm (y, i))).1 = h • y := by
    rw [he, e.apply_symm_apply]
  have hinj : Function.Injective f := by
    intro i j hij
    have hp : e (h • e.symm (y, i)) = e (h • e.symm (y, j)) :=
      Prod.ext ((hfst i).trans (hfst j).symm) hij
    have hx := (MulAction.injective h) (e.injective hp)
    exact (Prod.mk.inj (e.symm.injective hx)).2
  let p := Equiv.ofBijective f ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
  refine ⟨p, fun i => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  exact Prod.ext (hfst i) rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.FiberMeasure.Construction
