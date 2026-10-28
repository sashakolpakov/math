import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedLimit

/-! The point-mass coefficient in the distributional Newtonian Hessian. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem newtonian_radial_flux_at_zero (m : ℕ) {R : ℝ} (hR : 0 < R) :
    2 * (1 - (m : ℝ) / 2) * R ^ m * (R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1) = 2 - m := by
  have he : (R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1) = R ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    ring
  rw [he, ← Real.rpow_natCast R m]
  calc
    _ = 2 * (1 - (m : ℝ) / 2) * (R ^ (m : ℝ) * R ^ (-(m : ℝ))) := by ring
    _ = 2 * (1 - (m : ℝ) / 2) * 1 := by
      rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero]
    _ = _ := by ring

theorem tendsto_shiftedNewtonian_mass {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (i j : Fin m) :
    Tendsto (fun s : ℝ => ∫ y in ball 0 R,
      shiftedRadialHessian (1 - (m : ℝ) / 2) s y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) (𝓝[>] 0)
      (𝓝 (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0)) := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hp : ContinuousAt (fun s : ℝ => (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1)) 0 :=
      (continuousAt_id.add continuousAt_const).rpow_const
        (Or.inl (by simpa using (sq_pos_of_pos hR).ne'))
    have hc : ContinuousAt (fun s : ℝ => volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        (2 * (1 - (m : ℝ) / 2) * R ^ m * (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1))) 0 :=
      continuousAt_const.mul (continuousAt_const.mul hp)
    have ht := hc.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have ht' : Tendsto (fun s : ℝ => volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        (2 * (1 - (m : ℝ) / 2) * R ^ m * (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1)))
        (𝓝[>] 0) (𝓝 (volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m))) := by
      simpa only [zero_add, newtonian_radial_flux_at_zero m hR] using ht
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (shiftedRadialHessian_ball_mass hm _ hs hR.le i).symm
  · simp only [ite_eq_right hij]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun s => (shiftedRadialHessian_ball_offDiagonal _ s R i j hij).symm

end OAI.Analysis.PDE.Schauder
