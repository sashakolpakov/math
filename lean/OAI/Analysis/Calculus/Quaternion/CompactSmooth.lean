import OAI.Analysis.Calculus.Quaternion.CompactAverage

/-! Smoothness of finite compact averages of translates on an invariant open set. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open _root_.MeasureTheory
open scoped ContDiff Topology
universe u v
variable {E F : Type u} {α : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

omit [CompleteSpace F] in
theorem hasFDerivAt_integral_translate {O : Set E} (ho : IsOpen O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O)
    (s : α → E) (hs : Continuous s) (hO : ∀ x ∈ O, ∀ t, x + s t ∈ O)
    {x : E} (hx : x ∈ O) :
    HasFDerivAt (fun y => ∫ t, f (y + s t) ∂μ)
      (∫ t, fderiv ℝ f (x + s t) ∂μ) x := by
  have hft (y : E) (hy : y ∈ O) (t : α) :
      HasFDerivAt (fun z => f (z + s t)) (fderiv ℝ f (y + s t)) y := by
    have hd := (hf.differentiableOn (by simp) _ (hO y hy t)).differentiableAt
      (ho.mem_nhds (hO y hy t))
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      hd.hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (s t))
  have hcont : ContinuousOn (fun p : E × α => f (p.1 + s p.2)) (O ×ˢ Set.univ) :=
    hf.continuousOn.comp (continuous_fst.add (hs.comp continuous_snd)).continuousOn
      (fun p hp => hO p.1 hp.1 p.2)
  have hdcont : ContinuousOn (fun p : E × α =>
      fderiv ℝ (fun z => f (z + s p.2)) p.1) (O ×ˢ Set.univ) := by
    apply ((hf.continuousOn_fderiv_of_isOpen ho (by simp)).comp
      (continuous_fst.add (hs.comp continuous_snd)).continuousOn
      (fun p hp => hO p.1 hp.1 p.2)).congr
    intro p hp
    exact (hft p.1 hp.1 p.2).fderiv
  have h := hasFDerivAt_integral_compact ho (fun y t => f (y + s t)) hx hcont hdcont
    (fun y hy t => (hft y hy t).differentiableAt) (μ := μ)
  have he : (fun t => fderiv ℝ (fun y => f (y + s t)) x) =
      (fun t => fderiv ℝ f (x + s t)) := funext fun t => (hft x hx t).fderiv
  rw [he] at h
  exact h

theorem contDiffOn_integral_translate_nat (n : ℕ) {O : Set E} (ho : IsOpen O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O)
    (s : α → E) (hs : Continuous s) (hO : ∀ x ∈ O, ∀ t, x + s t ∈ O) :
    ContDiffOn ℝ n (fun y => ∫ t, f (y + s t) ∂μ) O := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivAt_integral_translate ho f hf s hs hO hx).continuousAt.continuousWithinAt
  | succ n ih =>
    have hd : DifferentiableOn ℝ (fun y => ∫ t, f (y + s t) ∂μ) O :=
      fun x hx => (hasFDerivAt_integral_translate ho f hf s hs hO hx).differentiableAt.differentiableWithinAt
    have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) O :=
      (contDiffOn_infty_iff_fderiv_of_isOpen ho).mp hf |>.2
    have hid := ih (fderiv ℝ f) hdf
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen ho]
    refine ⟨hd, by simp, ?_⟩
    apply hid.congr
    intro x hx
    exact (hasFDerivAt_integral_translate ho f hf s hs hO hx).fderiv

theorem contDiffOn_integral_translate {O : Set E} (ho : IsOpen O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O)
    (s : α → E) (hs : Continuous s) (hO : ∀ x ∈ O, ∀ t, x + s t ∈ O) :
    ContDiffOn ℝ ∞ (fun y => ∫ t, f (y + s t) ∂μ) O := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_integral_translate_nat n ho f hf s hs hO

end OAI.Analysis.Calculus.Quaternion
