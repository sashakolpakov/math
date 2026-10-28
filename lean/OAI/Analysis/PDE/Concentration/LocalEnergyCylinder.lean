import OAI.Analysis.PDE.Concentration.Lattice.Cylinder
import OAI.Analysis.PDE.Concentration.Packet.LocalEnergy

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open Laplacian InnerProductSpace Set
open scoped ContDiff Matrix.Norms.Elementwise

theorem corrected_local_energy_superharmonic {a : ℝ} {F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ}
    (hF : ContDiffOn ℝ ∞ F (physicalEnergyAnnulus a)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hweak : ∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * F z) ≤ δ * ∫ z, η z)
    (hn : ∀ z ∈ physicalEnergyAnnulus a, 0 ≤ F z)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ physicalEnergyAnnulus a) :
    0 ≤ F z + (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2) ∧
    Δ ((fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 => F y + (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2)) :
      OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ) z ≤ 0 := by
  have he (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
      16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2 = coordinateCylinderCorrection (0, 1) (0, 2) y := by
    rw [energyComplexTime_norm_sq]
    unfold coordinateCylinderCorrection
    ring
  simp_rw [he]
  apply corrected_energy_of_weak_bound (0, 1) (0, 2) (isOpen_physicalEnergyAnnulus a)
    (hF.of_le (by simp)) hδ hweak hz (hn z hz)
  rw [← energyComplexTime_norm_sq]
  have hnorm := norm_nonneg (OAI.Analysis.PDE.Green.energyComplexTime z)
  have hbound := hz.2
  nlinarith

/-- The cylinder bound uses only local smoothness of the actual energy on
the open annulus, with no smooth extension through either time boundary. -/
theorem exists_local_energy_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ a : ℝ, 0 < a → 4 * a ≤ 1 →
    ∀ F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiffOn ℝ ∞ F (physicalEnergyAnnulus a) →
    ∀ δ : ℝ, 0 ≤ δ →
    (∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * F z) ≤ δ * ∫ z, η z) →
    (∀ z ∈ physicalEnergyAnnulus a, 0 ≤ F z) → ∀ θ : ℝ,
    (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      F (cylinderEnergyEquiv (cylinderPoint t (2 * a) φ))) ≤
      C * (1 + |Real.log (2 * a)|) ^ 3 *
        (F (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ) := by
  obtain ⟨C, hC, hcylinder⟩ := exists_source_cylinder_concentration_constant
  refine ⟨C, hC, ?_⟩
  intro a ha ha4 F hF δ hδ hweak hn θ
  let G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ := fun z => F z + (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2)
  have hQ : ContDiff ℝ ∞ (fun z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 =>
      (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2)) := by
    simp_rw [energyComplexTime_norm_sq]
    fun_prop
  have hG : ContDiffOn ℝ ∞ G (physicalEnergyAnnulus a) := hF.add hQ.contDiffOn
  have hmem {x : CylinderSpace} (hx : x ∈ cylinderAnnulus a) :
      cylinderEnergyEquiv x ∈ physicalEnergyAnnulus a := by
    change x ∈ cylinderEnergyEquiv ⁻¹' physicalEnergyAnnulus a
    rwa [cylinderEnergyEquiv_preimage_annulus]
  have hGF {x : CylinderSpace} (hx : x ∈ cylinderAnnulus a) :
      F (cylinderEnergyEquiv x) ≤ G (cylinderEnergyEquiv x) := by
    have hz := hmem hx
    have hnorm := norm_nonneg (OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv x))
    have hbound := hz.2
    have hnonneg : 0 ≤ (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv x)‖ ^ 2) :=
      mul_nonneg (by positivity) (by nlinarith)
    dsimp [G]
    linarith
  have hnonneg : ∀ x ∈ cylinderAnnulus a, 0 ≤ (G ∘ cylinderEnergyEquiv) x := by
    intro x hx
    exact (hn _ (hmem hx)).trans (hGF hx)
  have hsuper : ∀ x ∈ cylinderAnnulus a, Δ (G ∘ cylinderEnergyEquiv) x ≤ 0 := by
    intro x hx
    rw [laplacian_comp_cylinderEnergyEquiv]
    exact (corrected_local_energy_superharmonic hF hδ hweak hn _ (hmem hx)).2
  have hbound := hcylinder a ha ha4 (G ∘ cylinderEnergyEquiv)
    (contDiffOn_comp_cylinderEnergyEquiv hG) hnonneg hsuper θ
  have hKU : cylinderShell 1 2 (2 * a) (2 * a) ⊆ cylinderAnnulus a := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hmono := cylinderTimeTrace_mono_on (isOpen_cylinderAnnulus a)
    (contDiffOn_comp_cylinderEnergyEquiv hF) (contDiffOn_comp_cylinderEnergyEquiv hG)
    (by positivity : 0 ≤ 2 * a) hKU (fun x hx => hGF (hKU hx))
  have hinitial : G (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) ≤
      F (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ := by
    have hq := mul_nonneg (div_nonneg hδ (by norm_num : (0 : ℝ) ≤ 4))
      (sq_nonneg ‖OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ))‖)
    dsimp [G]
    nlinarith
  have hlast := mul_le_mul_of_nonneg_left hinitial
    (show 0 ≤ C * (1 + |Real.log (2 * a)|) ^ 3 by positivity)
  simp only [cylinderAngularAverage, Function.comp_apply] at hmono hbound
  exact hmono.trans (hbound.trans hlast)


end OAI.Analysis.PDE.Concentration
