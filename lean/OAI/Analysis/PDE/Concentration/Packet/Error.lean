import OAI.Analysis.PDE.Concentration.Lattice.Jacobian
import OAI.Analysis.PDE.Concentration.Packet.Gradient
import OAI.Analysis.PDE.Concentration.Packet.Flux
import OAI.Analysis.PDE.Concentration.Input.Normalized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology Matrix.Norms.Elementwise

def packetFluxConstant (d : ℕ) : ℝ := 40 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2

def packetErrorConstant (n : ℕ) (G C : ℝ) : ℝ :=
  ((n : ℝ) + 3) * packetFluxConstant (n + 1) * G *
    OAI.Analysis.PDE.Green.physicalCutoffConstant (packetSpatialCoordinates n) * C

theorem packetErrorConstant_nonneg (n : ℕ) {G C : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) :
    0 ≤ packetErrorConstant n G C := by
  unfold packetErrorConstant packetFluxConstant
  exact mul_nonneg (mul_nonneg (by positivity) (OAI.Analysis.PDE.Green.physicalCutoffConstant_nonneg _)) hC

/-- Exact Jacobian cancellation and absorption of the derived boundary
error into the normalized input energy. -/
theorem packet_propagation_error_absorb (n : ℕ)
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    {h L E G C : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L)
    (hE : 0 ≤ E) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hlower : volume.real (physicalSpatialCell R) * h ^ (n + 2) ≤ C * E) :
    packetPropagationError (packetFullCoordinates n) (packetSpatialCoordinates n) R
      (packetFluxConstant (n + 1) * h ^ (55 * (n + 2) + 1))
      (G / h ^ (5 * (n + 2) + 1)) ≤
    packetErrorConstant n G C *
      (h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) * E) := by
  let D := ((n : ℝ) + 3) * packetFluxConstant (n + 1) * G *
    OAI.Analysis.PDE.Green.physicalCutoffConstant (packetSpatialCoordinates n)
  have hD : 0 ≤ D := mul_nonneg (by dsimp [packetFluxConstant]; positivity)
    (OAI.Analysis.PDE.Green.physicalCutoffConstant_nonneg _)
  have he : packetPropagationError (packetFullCoordinates n) (packetSpatialCoordinates n) R
      (packetFluxConstant (n + 1) * h ^ (55 * (n + 2) + 1))
      (G / h ^ (5 * (n + 2) + 1)) =
      D * (volume.real (physicalSpatialCell R) * h ^ (50 * (n + 2))) := by
    unfold packetPropagationError
    rw [abs_det_physicalCellLatticeMap]
    rw [show 55 * (n + 2) + 1 = 50 * (n + 2) + (5 * (n + 2) + 1) by omega, pow_add]
    dsimp only [D]
    push_cast
    field_simp
    ring
  rw [he]
  have hb := input_regularization_absorb (n + 1) hh hh1 hL ENNReal.toReal_nonneg hE hC hlower
  have hpow : L ^ (n + 3) ≤
      L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL
    push_cast
    have hp : 0 ≤ (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1) := by positivity
    linarith
  have hb' : volume.real (physicalSpatialCell R) * h ^ (50 * (n + 2)) ≤
      C * (h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) * E) :=
    hb.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg h)) hE) hC)
  exact (mul_le_mul_of_nonneg_left hb' hD).trans_eq (by dsimp [D, packetErrorConstant]; ring)

end OAI.Analysis.PDE.Concentration
