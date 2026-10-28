import OAI.Analysis.PDE.Concentration.Output.Pointwise
import OAI.Analysis.PDE.Concentration.Output.Scale
import OAI.Analysis.PDE.Concentration.PatchIntegral

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

/-- The manuscript's lower output-energy estimate in the actual rotated
Green cell. The full-ball recovery, nonlinear barrier, integration over the
physical patch, and cancellation of all semiclassical volume powers are
derived, rather than supplied as energy assumptions. -/
theorem packet_output_X0_lower {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1) (A N F B : ℝ)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ c h₀ L₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ),
      (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (Fintype.card ι : ℝ) ≤ N / h ^ (n + 2) →
      (∀ k, κ k ≤ F / h) → (∀ k, ‖(⟨cR k, cI k⟩ : ℂ)‖ ≤ B) →
      (∀ k, (∑ i, |v k i| ^ 2) ≤ 1 / 1600) →
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ,
      ContDiffOn ℝ 2 u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0} →
      ContinuousOn u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0} →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 → u x ≤ 0) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x)).PosSemidef) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x) =
        largeBackground (n + 1) h *
          (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re) →
      c * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) *
        (∫ y in physicalSpatialCell R,
          ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0))) y‖ ^
            (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      ∫ x in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z),
        (-u x) * (physicalLatticeCurrent R h (h * L) κ cR cI v
          (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re := by
  obtain ⟨c, C, h₀, L₀, hc, hC, hh₀, hh₀1, hL₀, hpoint⟩ :=
    packet_output_pointwise_gain hK hpos hv A N F B hA hN hF hB
  obtain ⟨v₀, hv₀, hvol⟩ := physicalOutputPatch_volume_semiclassical (n + 1)
  let p : ℝ := ((n : ℝ) + 2) / ((n : ℝ) + 1)
  have hp : 0 < p := by dsimp [p]; positivity
  refine ⟨c * v₀ / C ^ p, h₀, L₀, by positivity, hh₀, hh₀1, hL₀, ?_⟩
  intro R h L hh hsmall hL ι _ κ cR cI v hκ hm hf hs hcount hfreq hcoeff hvel
    z ht ht' u hu huc hu0 hPSD hPDE
  have hL0 : 0 < L := by linarith
  have ha : 0 < h * L := mul_pos hh hL0
  let τ := OAI.Analysis.PDE.Green.energyComplexTime z
  let P := physicalOutputPatch (d := n + 1) (h * L) τ (Real.sqrt L)⁻¹
  have hγ0 : 0 ≤ (Real.sqrt L)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg L)
  have hγ1 : (Real.sqrt L)⁻¹ ≤ (1 / 100 : ℝ) := by
    have h100 : 100 ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by norm_num) hL0.le]
      norm_num
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) h100
  have hPc : IsCompact P := isCompact_physicalOutputPatch (h * L) τ (Real.sqrt L)⁻¹ ha ht hγ0 hγ1
  have hPT := physicalOutputPatch_subset (d := n + 1) (h * L) τ (Real.sqrt L)⁻¹ ha ht hγ0 hγ1
  let den : ℝ := C * h ^ (2 * (n + 1)) * L ^ ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1))
  let w := packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0)))
  let g : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) → ℝ := fun y => (‖w y‖ ^ 2 / den) ^ p
  have hden : 0 < den := by dsimp [den]; positivity
  have hw : Continuous w := continuous_finiteWave _ _
  have hgc : Continuous g :=
    ((hw.norm.pow 2).div_const den).rpow_const (fun _ => Or.inr hp.le)
  let f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ := fun x => (-u x) *
    (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re
  have hfi := integrable_packet_weighted_physicalCell R h (h * L) hh ha κ cR cI v z ht huc
  have hf0 (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hx : spatialDefiningFunction (n + 1) (h * L) τ x < 0) : 0 ≤ f x := by
    apply mul_nonneg (neg_nonneg.mpr (hu0 x hx.le))
    apply le_of_lt
    apply physicalLatticeCurrent_time_pos R h (h * L) hh ha.ne' κ cR cI v
    · rw [physicalToNullCurrentPoint_fiber_imaginary]
      exact (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular (h * L) τ ha ht
        (hx.le.trans (by norm_num))).1
    · rw [physicalToNullCurrentPoint_fiber_imaginary]
      exact hx.le
  have hlow (y : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) (_hy : y ∈ closedPhysicalSpatialCell R)
      (q : Option (Fin (n + 1)) → ℂ) (hq : q ∈ P) :
      (c * h ^ 2) * g y ≤ f (spatialPacketEmbedding (n + 1) y q) :=
    hpoint R h L hh hsmall hL κ cR cI v hκ hm hf hs hcount hfreq hcoeff hvel
      z ht ht' u hu huc hu0 hPSD hPDE y q hq
  have hraw := physical_patch_integral_lower R (h * L) τ
    (OAI.Analysis.PDE.Green.isOpen_physical_fiber (h * L) τ ha ht).measurableSet
    hPc.measurableSet hPT hPc.measure_ne_top hfi
    (hgc.continuousOn.integrableOn_compact (isCompact_closedPhysicalSpatialCell R)) hf0
    (c * h ^ 2) hlow
  have hg0 : 0 ≤ ∫ y in physicalSpatialCell R, g y :=
    integral_nonneg (fun y => Real.rpow_nonneg (div_nonneg (sq_nonneg _) hden.le) p)
  have hvbound := hvol h L τ hh (hL₀.trans hL) ht ht'
  have hsmallvol := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hvbound (mul_nonneg hc.le (sq_nonneg h))) hg0
  have hbound := hsmallvol.trans hraw
  let D : ℝ := (C ^ p)⁻¹ * (h ^ (2 * (n + 2)))⁻¹ *
    L ^ (-p * ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1)))
  have hgeq : g = fun y => D * ‖w y‖ ^ (2 * p) := by
    funext y
    exact output_normalized_power n hC hh hL0 (norm_nonneg (w y))
  rw [hgeq, integral_const_mul] at hbound
  change (c * h ^ 2) * (v₀ * h ^ (2 * (n + 2)) * L ^ (n + 3)) *
    (D * (∫ y in physicalSpatialCell R, ‖w y‖ ^ (2 * p))) ≤ _ at hbound
  rw [← mul_assoc, output_volume_weight_scale n c v₀ C hh hL0] at hbound
  exact hbound

end OAI.Analysis.PDE.Concentration
