import OAI.Analysis.PDE.Elliptic.CubeGeometry

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem measurableSet_euclideanBox (B : Box ι) : MeasurableSet (euclideanBox B) :=
  B.measurableSet_coe.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).continuous.measurable

omit [Nonempty ι] in
theorem volume_coordinate_intersection (B : Box ι) {A : Set (EuclideanSpace ℝ ι)}
    (hA : MeasurableSet A) :
    volume ((WithLp.toLp 2 ⁻¹' A) ∩ (B : Set (ι → ℝ))) = volume (A ∩ euclideanBox B) := by
  have heq : WithLp.toLp 2 ⁻¹' (A ∩ euclideanBox B) =
      (WithLp.toLp 2 ⁻¹' A) ∩ (B : Set (ι → ℝ)) := by
    ext x
    simp [euclideanBox]
  rw [← heq]
  exact (PiLp.volume_preserving_toLp ι).measure_preimage
    (hA.inter (measurableSet_euclideanBox B)).nullMeasurableSet

/-- The dyadic open-set covering estimate in the actual Euclidean
norm and volume used by the elliptic differential operator. -/
theorem euclidean_dyadic_open_cover (B : Box ι)
    {A D : Set (EuclideanSpace ℝ ι)} (hA : IsOpen A) (hD : MeasurableSet D)
    {theta : ℝ≥0∞} (htheta : theta < 1)
    (hroot : volume (A ∩ euclideanBox B) ≤ theta * volume (euclideanBox B))
    (hparent : ∀ (w : List (Set ι)) (s : Set ι),
      theta * volume (euclideanBox ((dyadicBox B w).splitCenterBox s)) <
        volume (A ∩ euclideanBox ((dyadicBox B w).splitCenterBox s)) →
      euclideanBox (dyadicBox B w) ⊆ D) :
    volume (A ∩ euclideanBox B) ≤ theta * volume D := by
  have ht : Continuous (@WithLp.toLp 2 (ι → ℝ)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.continuous
  have hroot' : volume ((WithLp.toLp 2 ⁻¹' A) ∩ (B : Set (ι → ℝ))) ≤
      theta * volume (B : Set (ι → ℝ)) := by
    rw [volume_coordinate_intersection B hA.measurableSet, ← volume_euclideanBox B]
    exact hroot
  have h := dyadic_open_cover_volume B (hA.preimage ht) htheta hroot'
    (D := WithLp.toLp 2 ⁻¹' D) (fun w s hd ↦ by
      rw [volume_coordinate_intersection _ hA.measurableSet, ← volume_euclideanBox] at hd
      intro x hx
      exact hparent w s hd hx)
  rw [volume_coordinate_intersection B hA.measurableSet,
    (PiLp.volume_preserving_toLp ι).measure_preimage hD.nullMeasurableSet] at h
  exact h

end OAI.Analysis.PDE.Elliptic
