import OAI.Analysis.Calculus.Quaternion.CompactSmooth

/-! Smooth parameter dependence of a compact integral over a fixed domain.
The integrand need only be smooth on an open neighborhood of the parameterized
compact set, which is essential for the rational physical fiber coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
open scoped ContDiff Topology

universe u v
variable {E A F : Type u} {α : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

def partialFirstDerivative (f : E × A → F) (p : E × A) : E →L[ℝ] F :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E A)

omit [ProperSpace E] [CompleteSpace F] in
theorem contDiffOn_partialFirstDerivative {Ω : Set (E × A)} (hΩ : IsOpen Ω)
    {f : E × A → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (partialFirstDerivative f) Ω := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf).2.clm_comp contDiffOn_const

omit [ProperSpace E] [CompleteSpace F] in
theorem hasFDerivAt_first_section {Ω : Set (E × A)} (hΩ : IsOpen Ω)
    {f : E × A → F} (hf : ContDiffOn ℝ ∞ f Ω)
    (x : E) (a : A) (hxa : (x, a) ∈ Ω) :
    HasFDerivAt (fun y => f (y, a)) (partialFirstDerivative f (x, a)) x := by
  have hpair : HasFDerivAt (fun y : E => (y, a)) (ContinuousLinearMap.inl ℝ E A) x := by
    simpa using ((ContinuousLinearMap.inl ℝ E A).hasFDerivAt (x := x)).add_const ((0 : E), a)
  exact ((hf.differentiableOn (by simp) _ hxa).differentiableAt
    (hΩ.mem_nhds hxa)).hasFDerivAt.comp x hpair

omit [CompleteSpace F] in
theorem hasFDerivAt_compact_parametric_integral {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (f : E × A → F)
    (hf : ContDiffOn ℝ ∞ f Ω) (s : α → A) (hs : Continuous s)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t, f (y, s t) ∂μ)
      (∫ t, partialFirstDerivative f (x, s t) ∂μ) x := by
  have hmap : Continuous (fun p : E × α => (p.1, s p.2)) :=
    continuous_fst.prodMk (hs.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : E × α => (p.1, s p.2)) (U ×ˢ Set.univ) Ω :=
    fun p hp => hdom p.1 hp.1 p.2
  have hcont : ContinuousOn (fun p : E × α => f (p.1, s p.2)) (U ×ˢ Set.univ) :=
    hf.continuousOn.comp hmap.continuousOn hmaps
  have hdcont : ContinuousOn (fun p : E × α =>
      fderiv ℝ (fun y => f (y, s p.2)) p.1) (U ×ˢ Set.univ) := by
    apply ((contDiffOn_partialFirstDerivative hΩ hf).continuousOn.comp
      hmap.continuousOn hmaps).congr
    intro p hp
    exact (hasFDerivAt_first_section hΩ hf p.1 (s p.2) (hdom p.1 hp.1 p.2)).fderiv
  have h := OAI.Analysis.Calculus.Quaternion.hasFDerivAt_integral_compact hU (fun y t => f (y, s t)) hx hcont hdcont
    (fun y hy t => (hasFDerivAt_first_section hΩ hf y (s t) (hdom y hy t)).differentiableAt)
    (μ := μ)
  have he : (fun t => fderiv ℝ (fun y => f (y, s t)) x) =
      (fun t => partialFirstDerivative f (x, s t)) := funext fun t =>
    (hasFDerivAt_first_section hΩ hf x (s t) (hdom x hx t)).fderiv
  rw [he] at h
  exact h

theorem contDiffOn_compact_parametric_integral_nat (n : ℕ)
    {U : Set E} (hU : IsOpen U) {Ω : Set (E × A)} (hΩ : IsOpen Ω)
    (f : E × A → F) (hf : ContDiffOn ℝ ∞ f Ω)
    (s : α → A) (hs : Continuous s) (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) :
    ContDiffOn ℝ n (fun y => ∫ t, f (y, s t) ∂μ) U := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivAt_compact_parametric_integral hU hΩ f hf s hs hdom hx).continuousAt.continuousWithinAt
  | succ n ih =>
    have hd : DifferentiableOn ℝ (fun y => ∫ t, f (y, s t) ∂μ) U := fun x hx =>
      (hasFDerivAt_compact_parametric_integral hU hΩ f hf s hs hdom hx).differentiableAt.differentiableWithinAt
    have hid := ih (partialFirstDerivative f) (contDiffOn_partialFirstDerivative hΩ hf)
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hd, by simp, ?_⟩
    apply hid.congr
    intro x hx
    exact (hasFDerivAt_compact_parametric_integral hU hΩ f hf s hs hdom hx).fderiv

theorem contDiffOn_compact_parametric_integral
    {U : Set E} (hU : IsOpen U) {Ω : Set (E × A)} (hΩ : IsOpen Ω)
    (f : E × A → F) (hf : ContDiffOn ℝ ∞ f Ω)
    (s : α → A) (hs : Continuous s) (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) :
    ContDiffOn ℝ ∞ (fun y => ∫ t, f (y, s t) ∂μ) U := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_compact_parametric_integral_nat n hU hΩ f hf s hs hdom

end OAI.Analysis.PDE.Green
