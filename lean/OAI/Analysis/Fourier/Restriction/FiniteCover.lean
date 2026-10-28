import OAI.Analysis.Fourier.Restriction.FourierAmplitude

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Fourier bounds local to a finite measurable cover combine without any
assumption of disjointness of the covering sets. -/
theorem fourier_bound_of_finite_cover {n : ℕ} {ι : Type*}
    (I : Finset ι) (U : ι → Set (Space n)) (hUm : ∀ i, MeasurableSet (U i))
    (B : ι → ℝ≥0∞) {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hlocal : ∀ i ∈ I, ∀ g : Space n → ℂ, Measurable g → Integrable g →
      (∀ x, x ∉ U i → g x = 0) →
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier g) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ B i * eLpNorm g p volume)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ i ∈ I, x ∉ U i) → f x = 0) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (∑ i ∈ I, B i) * eLpNorm f p volume := by
  classical
  induction I using Finset.induction_on generalizing f with
  | empty =>
    have he : f = (fun _ ↦ 0) := funext fun x ↦ hfs x (by simp)
    have hF : OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun _ : Space n ↦ (0 : ℂ)) = (fun _ ↦ 0) := by
      funext ξ
      simp [OAI.Analysis.Fourier.LocalSmoothing.angularFourier]
    rw [he, hF]
    simp
  | @insert i I hi ih =>
    let g := (U i).indicator f
    let h := (U i)ᶜ.indicator f
    have hgm : Measurable g := hf.indicator (hUm i)
    have hhm : Measurable h := hf.indicator (hUm i).compl
    have hgi : Integrable g := hfi.indicator (hUm i)
    have hhi : Integrable h := hfi.indicator (hUm i).compl
    have hgsub : eLpNorm g p volume ≤ eLpNorm f p volume := by
      apply eLpNorm_mono hgm.aestronglyMeasurable
      intro x
      by_cases hx : x ∈ U i <;> simp [g, hx]
    have hhsub : eLpNorm h p volume ≤ eLpNorm f p volume := by
      apply eLpNorm_mono hhm.aestronglyMeasurable
      intro x
      by_cases hx : x ∈ U i <;> simp [h, hx]
    have hgs : ∀ x, x ∉ U i → g x = 0 := by
      intro x hx
      simp [g, hx]
    have hhs : ∀ x, (∀ j ∈ I, x ∉ U j) → h x = 0 := by
      intro x hx
      by_cases hxi : x ∈ U i
      · simp [h, hxi]
      · have hz : f x = 0 := hfs x (by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hxi
          · exact hx j hj)
        simp [h, hz]
    have Hg := hlocal i (Finset.mem_insert_self _ _) g hgm hgi hgs
    have Hh := ih (fun j hj ↦ hlocal j (Finset.mem_insert_of_mem hj)) hhm hhi hhs
    have hsum : f = (fun x ↦ g x + h x) := by
      funext x
      by_cases hx : x ∈ U i <;> simp [g, h, hx]
    have hF : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f = (fun ξ ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ + OAI.Analysis.Fourier.LocalSmoothing.angularFourier h ξ) := by
      funext ξ
      rw [hsum]
      exact angularFourier_add hgi hhi ξ
    rw [hF, Finset.sum_insert hi]
    calc
      _ ≤ eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier g) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) + eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier h) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := eLpNorm_add_le hq
      _ ≤ B i * eLpNorm g p volume + (∑ j ∈ I, B j) * eLpNorm h p volume := add_le_add Hg Hh
      _ ≤ B i * eLpNorm f p volume + (∑ j ∈ I, B j) * eLpNorm f p volume := by gcongr
      _ = _ := (add_mul _ _ _).symm

end OAI.Analysis.Fourier.Restriction
