import OAI.Analysis.PDE.Concentration.ExtendedEnergy
import OAI.Analysis.PDE.Concentration.Lattice.Cylinder

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open Laplacian
open scoped ContDiff Topology Matrix.Norms.Elementwise

/-- Cylinder concentration for the literal packet energy. The singular
explicit current and background are not assumed globally smooth. The weak
inequality and positivity are the separately proved energy inputs. -/
theorem exists_packetEnergy_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (ι : Type) [Fintype ι]
      (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ), 0 < h → 0 < a → 4 * a ≤ 1 →
    ∀ (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
      (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ), ContDiff ℝ ∞ u →
    let F := OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) u
    ∀ δ : ℝ, 0 ≤ δ →
    (∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * F z) ≤ δ * ∫ z, η z) →
    (∀ z ∈ physicalEnergyAnnulus a, 0 ≤ F z) → ∀ θ : ℝ,
    (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      F (cylinderEnergyEquiv (cylinderPoint t (2 * a) φ))) ≤
      C * (1 + |Real.log (2 * a)|) ^ 3 *
        (F (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ) := by
  obtain ⟨C, hC, hc⟩ := exists_latticeEnergy_cylinder_constant
  refine ⟨C, hC, ?_⟩
  intro d ι inst R h a hh ha ha4 κ cR cI v e lam u hu F δ hδ hw hn θ
  let A' := extendedPhysicalLatticeCurrent R h a ha κ cR cI v
  let B' := fun x => lam * extendedPhysicalBackground d a ha x
  let F' := OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A' B' u
  have heq (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) : F' z = F z :=
    extendedPhysical_energy_eq R h a ha κ cR cI v e lam u z hz
  have hw' (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ) (hη : ContDiff ℝ ∞ η)
      (hs : HasCompactSupport η) (haη : tsupport η ⊆ physicalEnergyAnnulus a)
      (hp : ∀ z, 0 ≤ η z) : (∫ z, Δ η z * F' z) ≤ δ * ∫ z, η z := by
    have hi : (∫ z, Δ η z * F' z) = ∫ z, Δ η z * F z := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : Δ η z = 0
      · simp only [hz, zero_mul]
      · rw [heq z (haη (OAI.Analysis.PDE.Green.laplacian_nonzero_mem_tsupport hz)).1.le]
    rw [hi]
    exact hw η hη hs haη hp
  have hn' (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ physicalEnergyAnnulus a) : 0 ≤ F' z := by
    rw [heq z hz.1.le]
    exact hn z hz
  have hb := hc d R a ha ha4 e lam A'
    (contDiff_extendedPhysicalLatticeCurrent R h a hh ha κ cR cI v)
    B' u (contDiff_const.mul (contDiff_extendedPhysicalBackground d a ha)) hu δ hδ hw' hn' θ
  have hcyl (t r φ : ℝ) (hr : a ≤ r) :
      F' (cylinderEnergyEquiv (cylinderPoint t r φ)) =
        F (cylinderEnergyEquiv (cylinderPoint t r φ)) := by
    apply heq
    simpa only [energyComplexTime_cylinderEnergyEquiv, cylinderComplexEquiv_point,
      Complex.norm_polarCoord_symm, abs_of_nonneg (ha.le.trans hr)] using hr
  have h2 : a ≤ 2 * a := by linarith
  have h4 : a ≤ 4 * a := by linarith
  change (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      F' (cylinderEnergyEquiv (cylinderPoint t (2 * a) φ))) ≤
    C * (1 + |Real.log (2 * a)|) ^ 3 *
      (F' (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ) at hb
  simp_rw [hcyl _ (2 * a) _ h2, hcyl _ (4 * a) _ h4] at hb
  exact hb

end OAI.Analysis.PDE.Concentration
