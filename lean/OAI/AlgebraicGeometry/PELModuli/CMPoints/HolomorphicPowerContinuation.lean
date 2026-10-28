import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Holomorphic Power Continuation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPowerContinuation

noncomputable section

section

/-! Holomorphic power maps propagate a chart expression from velocities
near zero to every velocity whose image belongs to the original chart. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [TopologicalSpace X]

theorem differentiableAt_of_holomorphic_power_coordinates
    (φ : P × V → X) (f : P × V → V) (e : OpenPartialHomeomorph X (P × V))
    (power : ℕ → X → X)
    (hpower : ∀ n, DifferentiableOn ℂ (fun z => e (power n (e.symm z)))
      (e.target ∩ (fun z => power n (e.symm z)) ⁻¹' e.source))
    (hopen : ∀ n, IsOpen
      (e.target ∩ (fun z => power n (e.symm z)) ⁻¹' e.source))
    (hscale : ∀ n : ℕ, 0 < n → ∀ q : P × V,
      power n (φ (q.1, (n : ℝ)⁻¹ • q.2)) = φ q)
    (B : Set P)
    (hcoord : ∀ q : P × V, q.1 ∈ B → φ q ∈ e.source → e (φ q) = (q.1, f q))
    (p₀ : P) (U : Set (P × V)) (hU : IsOpen U) (hzero : (p₀, (0 : V)) ∈ U)
    (hUB : ∀ q ∈ U, q.1 ∈ B) (hsource : ∀ q ∈ U, φ q ∈ e.source)
    (hf : DifferentiableOn ℂ f U)
    (v₀ : V) (hv₀ : φ (p₀, v₀) ∈ e.source) :
    DifferentiableAt ℂ f (p₀, v₀) := by
  have hlim : Tendsto (fun n : ℕ => (p₀, ((n : ℝ) + 1)⁻¹ • v₀))
      atTop (𝓝 (p₀, (0 : V))) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v₀
    simpa only [one_div, zero_smul] using tendsto_const_nhds.prodMk_nhds h
  obtain ⟨n, hn⟩ := (hlim.eventually (hU.mem_nhds hzero)).exists
  change (p₀, ((n : ℝ) + 1)⁻¹ • v₀) ∈ U at hn
  let k := n + 1
  have hk : 0 < k := Nat.succ_pos n
  let scale : P × V → P × V := fun q => (q.1, (k : ℝ)⁻¹ • q.2)
  have hmem : scale (p₀, v₀) ∈ U := by
    simpa only [scale, k, Nat.cast_add, Nat.cast_one] using hn
  have hscalar (v : V) : Complex.ofReal ((k : ℝ)⁻¹) • v = (k : ℝ)⁻¹ • v :=
    IsScalarTower.algebraMap_smul ℂ (k : ℝ)⁻¹ v
  have hdscale : Differentiable ℂ scale := by
    have heq : scale = (fun q : P × V =>
        (q.1, Complex.ofReal ((k : ℝ)⁻¹) • q.2)) := by
      funext q
      exact Prod.ext rfl (hscalar q.2).symm
    rw [heq]
    exact differentiable_fst.prodMk
      (differentiable_snd.const_smul (Complex.ofReal ((k : ℝ)⁻¹)))
  let z := fun q : P × V => (q.1, f (scale q))
  have hdz : DifferentiableAt ℂ z (p₀, v₀) :=
    differentiableAt_fst.prodMk ((hf.differentiableAt (hU.mem_nhds hmem)).comp _ hdscale.differentiableAt)
  have hz (q : P × V) (hq : scale q ∈ U) : z q = e (φ (scale q)) :=
    (hcoord (scale q) (hUB _ hq) (hsource _ hq)).symm
  have hzmem : z (p₀, v₀) ∈ e.target ∩
      (fun w => power k (e.symm w)) ⁻¹' e.source := by
    rw [hz _ hmem]
    refine ⟨e.map_source (hsource _ hmem), ?_⟩
    change power k (e.symm (e (φ (scale (p₀, v₀))))) ∈ e.source
    rw [e.left_inv (hsource _ hmem)]
    exact (hscale k hk (p₀, v₀)) ▸ hv₀
  have hd := ((hpower k).differentiableAt ((hopen k).mem_nhds hzmem)).comp _ hdz
  apply hd.snd.congr_of_eventuallyEq
  have hsmall := hdscale.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem)
  have hlarge := hdz.continuousAt.preimage_mem_nhds ((hopen k).mem_nhds hzmem)
  filter_upwards [hsmall, hlarge] with q hq hqD
  change f q = (e (power k (e.symm (z q)))).2
  rw [hz q hq, e.left_inv (hsource _ hq)]
  change f q = (e (power k (φ (q.1, (k : ℝ)⁻¹ • q.2)))).2
  rw [hscale k hk]
  have hbig : φ q ∈ e.source := by
    have h := hqD.2
    change power k (e.symm (z q)) ∈ e.source at h
    rw [hz q hq, e.left_inv (hsource _ hq)] at h
    exact (hscale k hk q) ▸ h
  exact (congrArg Prod.snd (hcoord q (hUB (scale q) hq) hbig)).symm

end

/-! A fixed open base neighborhood on which the actual exponential is
holomorphic everywhere that it meets the supplied total-space chart. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [TopologicalSpace X]

theorem exists_holomorphic_power_domain
    (φ : P × V → X) (f : P × V → V) (e : OpenPartialHomeomorph X (P × V))
    (power : ℕ → X → X)
    (hpower : ∀ n, DifferentiableOn ℂ (fun z => e (power n (e.symm z)))
      (e.target ∩ (fun z => power n (e.symm z)) ⁻¹' e.source))
    (hopen : ∀ n, IsOpen
      (e.target ∩ (fun z => power n (e.symm z)) ⁻¹' e.source))
    (hscale : ∀ n : ℕ, 0 < n → ∀ q : P × V,
      power n (φ (q.1, (n : ℝ)⁻¹ • q.2)) = φ q)
    (B₀ : Set P) (hB₀ : IsOpen B₀) (p₀ : P) (hp₀ : p₀ ∈ B₀)
    (hcoord : ∀ q : P × V, q.1 ∈ B₀ → φ q ∈ e.source → e (φ q) = (q.1, f q))
    (hcont : ContinuousOn φ (B₀ ×ˢ Set.univ))
    (U : Set (P × V)) (hU : IsOpen U) (hzero : (p₀, (0 : V)) ∈ U)
    (hf : DifferentiableOn ℂ f U) (hsource₀ : φ (p₀, 0) ∈ e.source) :
    ∃ B : Set P, IsOpen B ∧ p₀ ∈ B ∧ B ⊆ B₀ ∧
      IsOpen ((B ×ˢ Set.univ) ∩ φ ⁻¹' e.source) ∧
      DifferentiableOn ℂ f ((B ×ˢ Set.univ) ∩ φ ⁻¹' e.source) := by
  let O := (B₀ ×ˢ Set.univ) ∩ U
  have hO : IsOpen O := (hB₀.prod isOpen_univ).inter hU
  let W := O ∩ φ ⁻¹' e.source
  have hW : IsOpen W := (hcont.mono inter_subset_left).isOpen_inter_preimage hO e.open_source
  have hpW : (p₀, (0 : V)) ∈ W := ⟨⟨⟨hp₀, mem_univ 0⟩, hzero⟩, hsource₀⟩
  let B := {p : P | (p, (0 : V)) ∈ W}
  have hB : IsOpen B := hW.preimage (continuous_id.prodMk continuous_const)
  have hBB₀ : B ⊆ B₀ := fun _ hp => hp.1.1.1
  have hD : IsOpen ((B ×ˢ Set.univ) ∩ φ ⁻¹' e.source) :=
    (hcont.mono (Set.prod_mono hBB₀ subset_rfl)).isOpen_inter_preimage
      (hB.prod isOpen_univ) e.open_source
  refine ⟨B, hB, hpW, hBB₀, hD, ?_⟩
  intro q hq
  exact (differentiableAt_of_holomorphic_power_coordinates φ f e power hpower hopen hscale
    B₀ hcoord q.1 W hW hq.1.1 (fun _ hw => hw.1.1.1) (fun _ hw => hw.2)
    (hf.mono (fun _ hw => hw.1.2)) q.2 hq.2).differentiableWithinAt

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPowerContinuation
