import OAI.Analysis.Calculus.Coefficients.Derivative

open Set Filter _root_.MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Schauder

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smoothField_tendstoLocallyUniformly
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) :
    TendstoLocallyUniformly (fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) f atTop := by
  apply Metric.tendstoLocallyUniformly_iff.mpr
  intro ε hε x
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := x)) (ε/4) (by positivity)
  refine ⟨ball x (δ/2),ball_mem_nhds x (half_pos hδ),?_⟩
  filter_upwards [(OAI.Analysis.PDE.Schauder.standardMollifier_radius_tendsto m) (Iio_mem_nhds (half_pos hδ))] with j hj
  change (OAI.Analysis.PDE.Schauder.standardMollifier m j).rOut < δ/2 at hj
  intro z hz
  have hz' : dist z x < δ/2 := hz
  have hzx : dist z x < δ := lt_trans hz' (half_lt_self hδ)
  have hc := (OAI.Analysis.PDE.Schauder.standardMollifier m j).dist_normed_convolution_le (μ := volume)
    hf.aestronglyMeasurable (x₀ := z) (ε := ε/2) (fun y hy ↦ ?_)
  · change dist (f z) (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f z) < ε
    have hc' : dist (f z) (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f z) ≤ ε/2 := by
      simpa only [smoothField,dist_comm] using hc
    exact hc'.trans_lt (half_lt_self hε)
  · have hy' : dist y z < (OAI.Analysis.PDE.Schauder.standardMollifier m j).rOut := hy
    have hyx : dist y x < δ := by
      calc
        dist y x ≤ dist y z+dist z x := dist_triangle _ _ _
        _ < δ := by linarith
    calc
      dist (f y) (f z) ≤ dist (f y) (f x)+dist (f x) (f z) := dist_triangle _ _ _
      _ ≤ ε/2 := by
        have h1 := hclose hyx
        have h2 := hclose hzx
        rw [dist_comm (f x) (f z)]
        linarith

theorem smoothField_tendstoUniformlyOn_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) f atTop K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp (smoothField_tendstoLocallyUniformly f hf)) K hK

theorem smoothField_two_jet_tendstoUniformlyOn_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 2 f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) f atTop K ∧
    TendstoUniformlyOn (fun j ↦ fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f))
      (fderiv ℝ f) atTop K ∧
    TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f)))
      (fderiv ℝ (fderiv ℝ f)) atTop K := by
  let : CompleteSpace (EuclideanSpace ℝ (Fin m) →L[ℝ] F) := inferInstance
  let : CompleteSpace (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] F) := inferInstance
  refine ⟨smoothField_tendstoUniformlyOn_compact f hf.continuous hK,?_,?_⟩
  · simp_rw [fderiv_smoothField _ f (hf.of_le (by norm_num))]
    exact smoothField_tendstoUniformlyOn_compact _ (hf.continuous_fderiv (by norm_num)) hK
  · simp_rw [second_fderiv_smoothField _ f hf]
    exact smoothField_tendstoUniformlyOn_compact _
      ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).continuous_fderiv one_ne_zero) hK

end OAI.Analysis.Calculus.Coefficients
