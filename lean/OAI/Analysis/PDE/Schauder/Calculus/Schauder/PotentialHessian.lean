import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Distribution
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Reflection

/-! Identification of the actual Newtonian potential Hessian, including its point-mass term. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem newtonianPotential_hessian {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) {R : ℝ} (hR : 0 < R)
    (hsp : Function.support (fun y => f (x - y)) ⊆ ball 0 R) (i j : Fin m) :
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      (∫ y in ball 0 R, compensatedNewtonianEntry f x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) +
      f x * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0) := by
  have hg : ContDiff ℝ 2 (fun y => f (x - y)) := hf.comp (contDiff_const.sub contDiff_id)
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have h := newtonian_distribution_hessian hm (fun y => f (x - y)) hg hgc hR hsp i j
  rw [second_fderiv_newtonianPotential_apply (show 1 ≤ m by omega) f hf hfc]
  simpa only [newtonianPotential, second_fderiv_reflect_translate f hf,
    compensatedNewtonianEntry, finrank_euclideanSpace_fin, newtonianEntry, sub_zero] using h

end OAI.Analysis.PDE.Schauder
