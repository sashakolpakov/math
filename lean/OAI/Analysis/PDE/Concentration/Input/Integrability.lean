import OAI.Analysis.PDE.Concentration.Input.Density

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green
open scoped ContDiff Matrix Matrix.Norms.Elementwise

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

def closedPhysicalSpatialCell {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) : Set (OAI.Analysis.Calculus.Current.SpatialSpace d) :=
  (fun q => spatialCellMap R (spatialFromCoordinates q)) '' Icc (0 : Option (Fin d) → ℝ) 1

theorem isCompact_closedPhysicalSpatialCell {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    IsCompact (closedPhysicalSpatialCell R) :=
  isCompact_Icc.image ((spatialCellMap R).continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm.continuous)

theorem physicalSpatialCell_subset_closed {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    physicalSpatialCell R ⊆ closedPhysicalSpatialCell R := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.ofLp, ⟨fun i => (hy i).1.le, fun i => (hy i).2⟩, rfl⟩

/-- The actual packet density is integrable jointly over the finite physical
spatial cell and the complete imaginary fiber. This is derived from its
local smoothness and the actual compact fiber geometry. -/
theorem integrable_packet_input_density {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.Calculus.Current.Index d → ℝ)
    (τ : ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    Integrable (fun p : (Option (Fin d) → ℂ) × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (x - nullSpatialShift p.2) (OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)))
      ((volume.restrict {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0}).prod
        (volume.restrict (physicalSpatialCell R))) := by
  let S := {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0}
  have hS : IsCompact S := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a τ ha ht 0 (by norm_num)
  have htc : Continuous (OAI.Analysis.Calculus.Current.timeComponent (d := d)) := by
    unfold OAI.Analysis.Calculus.Current.timeComponent
    apply Continuous.div_const
    apply Quaternion.continuous_re.comp
    fun_prop
  have hf : ContinuousOn (fun p : (Option (Fin d) → ℂ) × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (x - nullSpatialShift p.2) (OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)))
      (S ×ˢ closedPhysicalSpatialCell R) := by
    intro p hp
    have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (hp.1.trans (show (0 : ℝ) ≤ 1 by norm_num))
    have hm : Continuous (fun p : (Option (Fin d) → ℂ) × OAI.Analysis.Calculus.Current.SpatialSpace d =>
        (x - nullSpatialShift p.2, OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)) :=
      (continuous_const.sub ((continuous_nullSpatialShift d).comp continuous_snd)).prodMk
        ((OAI.Analysis.Calculus.Current.contDiff_physicalEmbedding τ).continuous.comp continuous_fst)
    have hA := (latticeRegularizedCurrent_contDiffAt R h a hh κ cR cI v
        (x - nullSpatialShift p.2, OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)
        (show (x - nullSpatialShift p.2, OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1) ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d
          from hreg.1)).continuousAt
    have hcomp : ContinuousAt (fun p : (Option (Fin d) → ℂ) × OAI.Analysis.Calculus.Current.SpatialSpace d =>
        latticeRegularizedCurrent R h a κ cR cI v
          (x - nullSpatialShift p.2) (OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)) p :=
      hA.comp (x := p) (f := fun p : (Option (Fin d) → ℂ) × OAI.Analysis.Calculus.Current.SpatialSpace d =>
        (x - nullSpatialShift p.2, OAI.Analysis.Calculus.Current.physicalEmbedding τ p.1)) hm.continuousAt
    exact (htc.continuousAt.comp hcomp).continuousWithinAt
  have hi := (hf.integrableOn_compact (μ := volume) (hS.prod (isCompact_closedPhysicalSpatialCell R))).mono_set
    (Set.prod_mono (show {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} ⊆ S from
      by intro q hq; exact (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0 from hq).le)
      (physicalSpatialCell_subset_closed R))
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hi

/-- Bounded nonnegative weights may be inserted into the two successive
integrals. Neither continuity nor integrability of the weight is needed. -/
theorem weighted_double_integral_le {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    {f : E × F → ℝ} (hf : Integrable f (μ.prod ν))
    (hn : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, 0 ≤ f (x, y)) {w : E → F → ℝ} {B : ℝ}
    (hw : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, 0 ≤ w x y ∧ w x y ≤ B) :
    (∫ x, ∫ y, w x y * f (x, y) ∂ν ∂μ) ≤ B * ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  have hle : ∀ᵐ x ∂μ, (∫ y, w x y * f (x, y) ∂ν) ≤ B * ∫ y, f (x, y) ∂ν := by
    filter_upwards [hf.prod_right_ae, hn, hw] with x hx hnx hwx
    have h := integral_mono_of_nonneg
      (by filter_upwards [hnx, hwx] with y hny hwy; exact mul_nonneg hwy.1 hny)
      (hx.const_mul B)
      (by filter_upwards [hnx, hwx] with y hny hwy; exact mul_le_mul_of_nonneg_right hwy.2 hny)
    simpa only [integral_const_mul] using h
  have h := integral_mono_of_nonneg
    (by
      filter_upwards [hn, hw] with x hnx hwx
      apply integral_nonneg_of_ae
      filter_upwards [hnx, hwx] with y hny hwy
      exact mul_nonneg hwy.1 hny)
    (hf.integral_prod_left.const_mul B) hle
  simpa only [integral_const_mul] using h

end OAI.Analysis.PDE.Concentration
