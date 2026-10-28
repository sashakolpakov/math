import OAI.Analysis.PDE.Green.ParametricIntegral

/-! Differentiating smooth compact kernels against a merely continuous weight.+No derivative of the weight is required. -/

noncomputable section
open _root_.MeasureTheory Set
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green

universe u v
variable {E A F : Type u} {T : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace T] [CompactSpace T] [T2Space T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]

omit [CompleteSpace F] in
theorem hasFDerivAt_weighted_kernel_integral {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (K : E × A → F)
    (hK : ContDiffOn ℝ ∞ K Ω) (s : T → A) (hs : Continuous s)
    (w : T → ℝ) (hw : Continuous w)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t, w t • K (y, s t) ∂μ)
      (∫ t, w t • OAI.Analysis.PDE.Green.partialFirstDerivative K (x, s t) ∂μ) x := by
  have hmap : Continuous (fun p : E × T => (p.1, s p.2)) :=
    continuous_fst.prodMk (hs.comp continuous_snd)
  have hmaps : MapsTo (fun p : E × T => (p.1, s p.2)) (U ×ˢ univ) Ω :=
    fun p hp => hdom p.1 hp.1 p.2
  have hcont : ContinuousOn (fun p : E × T => w p.2 • K (p.1, s p.2)) (U ×ˢ univ) :=
    (hw.comp continuous_snd).continuousOn.smul (hK.continuousOn.comp hmap.continuousOn hmaps)
  have hd (y : E) (hy : y ∈ U) (t : T) :
      HasFDerivAt (fun z => w t • K (z, s t)) (w t • OAI.Analysis.PDE.Green.partialFirstDerivative K (y, s t)) y :=
    (OAI.Analysis.PDE.Green.hasFDerivAt_first_section hΩ hK y (s t) (hdom y hy t)).const_smul (w t)
  have hdcont : ContinuousOn (fun p : E × T =>
      fderiv ℝ (fun z => w p.2 • K (z, s p.2)) p.1) (U ×ˢ univ) := by
    apply ((hw.comp continuous_snd).continuousOn.smul
      ((OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK).continuousOn.comp hmap.continuousOn hmaps)).congr
    intro p hp
    exact (hd p.1 hp.1 p.2).fderiv
  have h := OAI.Analysis.Calculus.Quaternion.hasFDerivAt_integral_compact hU (fun y t => w t • K (y, s t)) hx hcont hdcont
    (fun y hy t => (hd y hy t).differentiableAt) (μ := μ)
  have he : (fun t => fderiv ℝ (fun y => w t • K (y, s t)) x) =
      (fun t => w t • OAI.Analysis.PDE.Green.partialFirstDerivative K (x, s t)) := funext fun t => (hd x hx t).fderiv
  rw [he] at h
  exact h

theorem contDiffOn_weighted_kernel_integral_nat (n : ℕ) {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (K : E × A → F)
    (hK : ContDiffOn ℝ ∞ K Ω) (s : T → A) (hs : Continuous s)
    (w : T → ℝ) (hw : Continuous w)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) :
    ContDiffOn ℝ n (fun y => ∫ t, w t • K (y, s t) ∂μ) U := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivAt_weighted_kernel_integral hU hΩ K hK s hs w hw hdom hx).continuousAt.continuousWithinAt
  | succ n ih =>
    have hd : DifferentiableOn ℝ (fun y => ∫ t, w t • K (y, s t) ∂μ) U := fun x hx =>
      (hasFDerivAt_weighted_kernel_integral hU hΩ K hK s hs w hw hdom hx).differentiableAt.differentiableWithinAt
    have hid := ih (OAI.Analysis.PDE.Green.partialFirstDerivative K) (OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK)
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hd, by simp, ?_⟩
    apply hid.congr
    intro x hx
    exact (hasFDerivAt_weighted_kernel_integral hU hΩ K hK s hs w hw hdom hx).fderiv

theorem contDiffOn_weighted_kernel_integral {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (K : E × A → F)
    (hK : ContDiffOn ℝ ∞ K Ω) (s : T → A) (hs : Continuous s)
    (w : T → ℝ) (hw : Continuous w)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) :
    ContDiffOn ℝ ∞ (fun y => ∫ t, w t • K (y, s t) ∂μ) U := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_weighted_kernel_integral_nat n hU hΩ K hK s hs w hw hdom

end OAI.Analysis.PDE.Schauder
