import OAI.Analysis.PDE.Green.ActualSmooth
import OAI.Analysis.PDE.Energy.CellComparison
import OAI.Analysis.PDE.Green.FiberHessian

/-! Identification of the full-coordinate combined energy with the spatial
determinant-segment energy to which periodic-cell Green's identity applies. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_fiberSection {n s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    {k : ℕ∞ω} (hf : ContDiff ℝ k f) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) :
    ContDiff ℝ k (fun y => f (fiberEmbedding n s z y)) :=
  hf.comp ((contDiff_fiberEmbedding n s k).comp (contDiff_const.prodMk contDiff_id))

theorem determinantSegmentEnergy_fiber_eq {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (V : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) :
    OAI.Analysis.PDE.Energy.determinantSegmentEnergy e V
      (fun y => B (fiberEmbedding n s z y)) (fun y => u (fiberEmbedding n s z y)) =
    ∫ y in V, spatialPencilEnergyDensity e B u (fiberEmbedding n s z y) := by
  rw [OAI.Analysis.PDE.Energy.determinantSegmentEnergy_eq_potential_integral e V
    (contDiff_fiberSection hB z) (contDiff_fiberSection hu z)]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold spatialPencilEnergyDensity
  apply congrArg (fun v : ℝ => u (fiberEmbedding n s z y) * v)
  apply intervalIntegral.integral_congr
  intro t ht
  have hseg : ContDiff ℝ 2 (fun x => B x + t * u x) :=
    hB.add (contDiff_const.mul hu)
  have h := quaternionHessian_fiberEmbedding e hseg z y
  simpa only [smul_eq_mul] using congrArg (OAI.LinearAlgebra.Moore.mooreDet n) h

theorem setFiberCombinedEnergy_eq_spatial {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)} {V : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (hV : Bornology.IsBounded V)
    (hfiber : (fiberEmbedding n s z) ⁻¹' S = V)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : Continuous A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) :
    setFiberCombinedEnergy e lam S A B u z =
      (∫ y in V, (-u (fiberEmbedding n s z y)) * (A (fiberEmbedding n s z y) 0 0).re) +
      OAI.Analysis.PDE.Energy.determinantSegmentEnergy e V
        (fun y => B (fiberEmbedding n s z y)) (fun y => u (fiberEmbedding n s z y)) / lam := by
  have hf : Continuous (fiberEmbedding n s z) :=
    (continuous_fiberEmbedding n s).comp (continuous_const.prodMk continuous_id)
  have hm : IntegrableOn (fun y => (-u (fiberEmbedding n s z y)) *
      (A (fiberEmbedding n s z y) 0 0).re) V :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hV
      ((hu.continuous.comp hf).neg.mul ((continuous_current_mass hA).comp hf))
  have he : IntegrableOn (fun y =>
      spatialPencilEnergyDensity e B u (fiberEmbedding n s z y)) V :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hV
      ((continuous_spatialPencilEnergyDensity e hB hu).comp hf)
  unfold setFiberCombinedEnergy combinedEnergyDensity
  rw [hfiber, integral_add hm (he.const_mul _), integral_const_mul,
    determinantSegmentEnergy_fiber_eq e V (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) z]
  ring

end OAI.Analysis.PDE.Green
