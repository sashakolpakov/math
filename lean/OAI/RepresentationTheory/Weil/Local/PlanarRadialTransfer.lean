import OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact
import OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase

/-! # Planar Radial Transfer -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer.Construction

noncomputable section

/-! Moving the planar quadratic phase's Laplacian to a radial amplitude. -/

open _root_.MeasureTheory

def planarRadialTransferIntegrable (b : ℝ) (F F' F'' : ℝ → ℂ) : Prop :=
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialX F' * PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialXX F' F'' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialX F' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialY F' * PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialYY F' F'' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialY F' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b)

theorem planar_radial_quadratic_integral_transfer
    (b : ℝ) (F F' F'' : ℝ → ℂ)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t)
    (hF' : ∀ t, 0 ≤ t → HasDerivAt F' (F'' t) t)
    (hI : planarRadialTransferIntegrable b F F' F'') :
    -(b : ℂ) ^ 2 * (∫ z, (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F (PlanarRadialCompact.Construction.planarRadiusSquared z) *
      PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) =
      ∫ z, ((PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F'' (PlanarRadialCompact.Construction.planarRadiusSquared z) +
        F' (PlanarRadialCompact.Construction.planarRadiusSquared z)) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hI
  have hx := OscillatoryTailTools.Construction.integral_planar_second_derivative_transfer
    (PlanarRadialCompact.Construction.planarRadial F) (PlanarRadialCompact.Construction.planarRadialX F') (PlanarRadialCompact.Construction.planarRadialXX F' F'')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b)
    (PlanarRadialCompact.Construction.planarRadial_hasDerivAt_x F F' hF) (PlanarRadialCompact.Construction.planarRadialX_hasDerivAt_x F' F'' hF')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase_hasDerivAt_x b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseX_hasDerivAt_x b)
    h1 h2 h3 h4 h5
  have hy := OscillatoryTailTools.Construction.integral_planar_second_derivative_transfer_right
    (PlanarRadialCompact.Construction.planarRadial F) (PlanarRadialCompact.Construction.planarRadialY F') (PlanarRadialCompact.Construction.planarRadialYY F' F'')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b)
    (PlanarRadialCompact.Construction.planarRadial_hasDerivAt_y F F' hF) (PlanarRadialCompact.Construction.planarRadialY_hasDerivAt_y F' F'' hF')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase_hasDerivAt_y b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseY_hasDerivAt_y b)
    h6 h7 h8 h9 h10
  have hsum : (∫ z, PlanarRadialCompact.Construction.planarRadial F z *
      (PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b z + PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b z)) =
      ∫ z, (PlanarRadialCompact.Construction.planarRadialXX F' F'' z + PlanarRadialCompact.Construction.planarRadialYY F' F'' z) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
    simp_rw [mul_add, add_mul]
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadial F z * PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b z) at h1
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadial F z * PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b z) at h6
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadialXX F' F'' z * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) at h3
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadialYY F' F'' z * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) at h8
    rw [integral_add h1 h6, integral_add h3 h8, hx, hy]
  simp_rw [PlanarQuadraticPhase.Construction.planarQuadraticPhase_laplacian, PlanarRadialCompact.Construction.planarRadial_laplacian] at hsum
  have heq : (-4 * (b : ℂ) ^ 2) *
      (∫ z, (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F (PlanarRadialCompact.Construction.planarRadiusSquared z) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) =
      4 * ∫ z, ((PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F'' (PlanarRadialCompact.Construction.planarRadiusSquared z) +
        F' (PlanarRadialCompact.Construction.planarRadiusSquared z)) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
    convert hsum using 1
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold PlanarRadialCompact.Construction.planarRadial PlanarRadialCompact.Construction.planarRadiusSquared
        push_cast
        ring
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
  linear_combination (1 / 4 : ℂ) * heq

end

end OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer.Construction
