import OAI.Geometry.ComplexTorus.RiemannProjectivity.DirectionalJetsOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularZero
import OAI.Geometry.ComplexTorus.RiemannProjectivity.IdentityEq

/-! # Holomorphic Zero -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicZero.Constructions.HolomorphicZeroDimension

noncomputable section

/-!
# RiemannProjectivity: Hausdorff dimension of holomorphic zero sets

A countable dense family of complex directions detects every nonflat zero.
Finite-order directional jets cover those zeros by countably many regular
holomorphic zero sets. The regular dimension bound therefore also holds at
singular zeros.
-/

open Set Filter _root_.Metric _root_.Module
open scoped _root_.Topology ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem exists_nonzero_line_in_dense_directions {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hnot : ¬∀ᶠ y in 𝓝 x, f y = 0) {D : Set V} (hD : Dense D) :
    ∃ v ∈ D, ¬∀ᶠ t : ℂ in 𝓝 0, f (x + t • v) = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hmaps : MapsTo (fun v : V => x + v) (ball 0 (r / 2)) U := by
    intro v hv
    apply hball
    have hnorm : ‖v‖ < r / 2 := by simpa only [mem_ball, dist_zero_right] using hv
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm.trans (half_lt_self hr)
  have hfc : ContinuousOn (fun v => f (x + v)) (ball 0 (r / 2)) :=
    hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  let O := ball (0 : V) (r / 2) ∩ (fun v => f (x + v)) ⁻¹' ({0} : Set ℂ)ᶜ
  have hO : IsOpen O := hfc.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hOne : O.Nonempty := by
    by_contra hno
    apply hnot
    filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
    by_contra hfy
    apply hno
    refine ⟨y - x, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hy
    · simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff, add_sub_cancel] using hfy
  obtain ⟨v, hvO, hvD⟩ := hD.inter_open_nonempty O hO hOne
  refine ⟨v, hvD, ?_⟩
  intro hzero
  have hv : ‖v‖ < r / 2 := by simpa only [mem_ball, dist_zero_right] using hvO.1
  let line : ℂ → V := fun t => x + t • v
  have hline : Differentiable ℂ line := (differentiable_id.smul_const v).const_add x
  have hlineU : MapsTo line (ball (0 : ℂ) 2) U := by
    intro t ht
    apply hball
    have ht2 : ‖t‖ < 2 := by simpa only [mem_ball, dist_zero_right] using ht
    change dist (x + t • v) x < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg v]
  have hga := (hf.comp hline.differentiableOn hlineU).analyticOnNhd isOpen_ball
  have hall := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (mem_ball_self (by norm_num : (0 : ℝ) < 2))
    (hzero.filter_mono nhdsWithin_le_nhds).frequently
  have h1 := hall (show (1 : ℂ) ∈ ball 0 2 by norm_num [mem_ball, dist_zero_right])
  apply hvO.2
  simpa only [Function.comp_apply, line, one_smul, Pi.zero_apply, mem_singleton_iff] using h1

theorem zero_dimension_of_nonflat {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hnot : ∀ x ∈ U, ¬∀ᶠ y in 𝓝 x, f y = 0) :
    dimH {x | x ∈ U ∧ f x = 0} ≤ ((finrank ℝ V - 2 : ℕ) : ℝ≥0∞) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : SecondCountableTopology V := inferInstance
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense V
  let : Countable D := hDc.to_subtype
  let S : D → ℕ → Set V := fun v n =>
    {x | x ∈ U ∧ DirectionalJetsOn.Constructions.DirectionalJets.jet f v.val n x = 0 ∧
      Function.Surjective (fderiv ℂ (DirectionalJetsOn.Constructions.DirectionalJets.jet f v.val n) x)}
  have hcover : {x | x ∈ U ∧ f x = 0} ⊆ ⋃ v : D, ⋃ n : ℕ, S v n := by
    intro x hx
    obtain ⟨v, hvD, hv⟩ := exists_nonzero_line_in_dense_directions hU hf hx.1 (hnot x hx.1) hDd
    obtain ⟨n, hn, hreg⟩ := DirectionalJetsOn.Constructions.DirectionalJets.exists_regular_jet_of_nonzero_line hU hf hx.1 hx.2 v hv
    exact mem_iUnion.mpr ⟨⟨v, hvD⟩, mem_iUnion.mpr ⟨n, hx.1, hn, hreg⟩⟩
  apply (dimH_mono hcover).trans
  simp only [dimH_iUnion]
  apply iSup_le
  intro v
  apply iSup_le
  intro n
  exact RegularZero.Constructions.RegularZeroDimension.regular_zero_dimension hU (DirectionalJetsOn.Constructions.DirectionalJets.differentiableOn_jet hU hf v.val n)

/-- A nonzero holomorphic function on a connected open complex domain has
a zero set of real Hausdorff dimension at most ambient dimension minus two. -/
theorem zero_dimension {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hne : ∃ x ∈ U, f x ≠ 0) :
    dimH {x | x ∈ U ∧ f x = 0} ≤ ((finrank ℝ V - 2 : ℕ) : ℝ≥0∞) := by
  apply zero_dimension_of_nonflat hU hf
  intro x hx hzero
  obtain ⟨z, hz, hzn⟩ := hne
  exact hzn (IdentityEq.Constructions.Identity.eq_zero_of_zero_germ hU hconn hf hx hzero z hz)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicZero.Constructions.HolomorphicZeroDimension
