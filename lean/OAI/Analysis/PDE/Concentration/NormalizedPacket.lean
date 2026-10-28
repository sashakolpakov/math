import OAI.Analysis.PDE.Concentration.Packet.Restricted
import OAI.Analysis.PDE.Concentration.Packet.Error

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

/-- Complete normalized sector concentration, with all current, energy,
cylinder, gradient, flux and normalization estimates proved internally.
The sole PDE input is a genuine smooth periodic Dirichlet solution. -/
theorem normalized_packet_concentration {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ c C h₀ L₀ B : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧ 0 < B ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L → B * Real.log h⁻¹ ≤ L → 4 * (h * L) ≤ 1 →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      (∀ b < (1 : ℝ), ∃ y, b < ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) →
      ∀ _ : PhysicalPacketSolution R h (h * L) κ cR cI v (largeBackground (n + 1) h),
      c * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) *
        (∫ t in (1 : ℝ)..2, ∫ y in physicalSpatialCell R,
          ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) t) y‖ ^
            (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      C * (1 + |Real.log (2 * (h * L))|) ^ 3 *
        (h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2)) := by
  obtain ⟨c, C, h₀, L₀, hc, hC, hh₀, hh₀1, hL₀, hmain⟩ :=
    packet_restricted_bound_from_solution hK hpos hcap A hA
  obtain ⟨G, hG, hgrad⟩ := normalized_packet_boundary_gradient hK hcap
  obtain ⟨h₁, B, hh₁, hh₁1, hB, hflux⟩ :=
    normalized_packet_boundary_flux hK hpos hcap (55 * (n + 2) + 1)
  obtain ⟨CN, hCN, hnormlower⟩ := compact_angular_energy_lower hK
  let D := packetErrorConstant n G CN
  have hD : 0 ≤ D := packetErrorConstant_nonneg n hG.le hCN.le
  refine ⟨c, C * (1 + D), min h₀ h₁, L₀, B, hc, by positivity,
    lt_min hh₀ hh₁, (min_le_left _ _).trans hh₀1, hL₀, hB, ?_⟩
  intro R hR h L hh hsmall hL hlog ha4 ι inst κ cR cI v m hinj hκ hm hf hs hnorm hnorm' S
  have hsmall₀ := hsmall.trans (min_le_left h₀ h₁)
  have hsmall₁ := hsmall.trans (min_le_right h₀ h₁)
  have hh1 := hsmall₀.trans hh₀1
  have hL1 : 1 ≤ L := by linarith
  have hha : h ≤ h * L := by nlinarith
  let ε := packetFluxConstant (n + 1) * h ^ (55 * (n + 2) + 1)
  let Γ := G / h ^ (5 * (n + 2) + 1)
  have hε : 0 ≤ ε := by dsimp [ε, packetFluxConstant]; positivity
  have hΓ : 0 ≤ Γ := by dsimp [Γ]; positivity
  have hfg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3)
      (ht : h * L < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4)
      (hr : OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L) x = 0) :
      ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots S.u x‖ ≤ Γ :=
    hgrad R hR h (h * L) κ cR cI v m (largeBackground (n + 1) h) hh hh1 hha
      (largeBackground_pos (n + 1) hh).le hinj hκ hm hf hnorm S x ht hr
  have hff (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3)
      (ht : h * L < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4)
      (hr : OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L) x = 0) :
      ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L)) x) ᵥ*
        physicalLatticeCurrent R h (h * L) κ cR cI v x‖ ≤ ε := by
    exact hflux R hR h L κ cR cI v m hh hsmall₁ hL1 hlog hinj hκ hm hf hnorm x ht.1.le hr
  have hestimate := hmain R hR h L hh hsmall₀ hL ha4 κ cR cI v m hinj hκ hm hf hs
    hnorm hnorm' S ε Γ hε hΓ hff hfg
  have hlower := hnormlower R hR h hh hh1 (fun i => packetSpatialFrequency (κ i) (v i)) m
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) 0)
    hinj hf hm hnorm'
  change volume.real (physicalSpatialCell R) * h ^ (n + 2) ≤
    CN * ∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2 at hlower
  have herr := packet_propagation_error_absorb n R hh hh1 hL1
    (integral_nonneg fun _ => sq_nonneg _) hG.le hCN.le hlower
  let H := h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
    (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2)
  have herr' : packetPropagationError (packetFullCoordinates n) (packetSpatialCoordinates n)
      R ε Γ ≤ D * H := herr
  apply hestimate.trans
  calc
    _ ≤ C * (1 + |Real.log (2 * (h * L))|) ^ 3 * ((1 + D) * H) :=
      mul_le_mul_of_nonneg_left (by nlinarith [herr']) (by positivity)
    _ = _ := by dsimp only [H]; ring

end OAI.Analysis.PDE.Concentration
