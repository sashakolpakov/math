import OAI.Geometry.Nikodym.Coordinates
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Geometry.Nikodym

def projectiveJoinIsometry (d : ℕ) : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space (d+1) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (Space d × ℝ)).trans (projectiveJoinLinear d)
  norm_map' p := by
    change ‖projectiveJoin d (WithLp.ofLp p)‖ = ‖p‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [projectiveJoin_norm_sq,WithLp.prod_norm_sq_eq_of_L2]
    rfl

theorem measurePreserving_projectiveJoin (d : ℕ) :
    MeasurePreserving (projectiveJoin d) volume volume := by
  have h := (projectiveJoinIsometry d).measurePreserving.comp
    (WithLp.volume_preserving_toLp (U:=Space d) (V:=ℝ))
  convert h using 1
  funext p
  rfl

theorem measurePreserving_projectiveJoin_symm (d : ℕ) :
    MeasurePreserving (projectiveJoin d).symm volume volume := by
  have h := (WithLp.volume_preserving_ofLp (U:=Space d) (V:=ℝ)).comp
    (projectiveJoinIsometry d).symm.measurePreserving
  convert h using 1
  funext x
  rfl

@[simp] theorem map_projectiveJoin_symm_volume (d : ℕ) :
    Measure.map (projectiveJoin d).symm volume = volume :=
  (measurePreserving_projectiveJoin_symm d).map_eq

end OAI.Geometry.Nikodym
