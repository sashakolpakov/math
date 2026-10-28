import OAI.Analysis.PDE.Variational.CellL2
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Constructions.Pi

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

theorem countable_regular_zeros {f : ℝ→ℝ} (hf : Differentiable ℝ f) :
    {x | f x=0 ∧ deriv f x≠0}.Countable := by
  apply (countable_setOfPred_isolated_right_within (s:={x | f x=0})).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [← Filter.eventually_false_iff_eq_bot]
  have hn := (hf x).hasDerivAt.eventually_ne (c:=f x) hx.2
  have hn' : ∀ᶠ y in 𝓝[{y | f y=0}∩Ioi x] x, f y≠f x :=
    hn.filter_mono (nhdsWithin_mono _ (fun y hy ↦ ne_of_gt hy.2))
  filter_upwards [hn', self_mem_nhdsWithin] with y hy hz
  exact hy (hz.1.trans hx.1.symm)

theorem deriv_zero_ae_on_level {f : ℝ→ℝ} (hf : Differentiable ℝ f) :
    ∀ᵐ x ∂volume, f x=0 → deriv f x=0 := by
  have hzero : volume {x | f x=0 ∧ deriv f x≠0}=0 :=
    (countable_regular_zeros hf).measure_zero volume
  have ha : ∀ᵐ x ∂volume, x∉{x | f x=0 ∧ deriv f x≠0} :=
    ae_iff.mpr (by simpa using hzero)
  filter_upwards [ha] with x hx hfx
  by_contra hd
  exact hx ⟨hfx,hd⟩

variable {m : ℕ}

theorem hasDerivAt_insertNth (j : Fin (m+1)) (y : Fin m→ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (j.insertNth s y : CellCoordinates m)) (Pi.single j 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i=j
  · subst i
    simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
    exact hasDerivAt_id' t
  · obtain ⟨l,rfl⟩ := i.exists_succAbove_eq hi
    simpa using hasDerivAt_const t (y l)

theorem cellGradient_zero_ae_on_level {u : CellCoordinates m→ℝ} (hu : ContDiff ℝ 1 u) :
    ∀ᵐ x ∂volume, u x=0 → cellGradient u x=0 := by
  have hj (j : Fin (m+1)) : ∀ᵐ x ∂volume, u x=0 → cellGradient u x j=0 := by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) ↦ ℝ) j
    have hp : MeasurableSet {x : CellCoordinates m | u x=0 → cellGradient u x j=0} := by
      simp only [imp_iff_not_or]
      exact (isClosed_eq hu.continuous continuous_const).measurableSet.compl.union
        (isClosed_eq (OAI.Analysis.PDE.Green.continuous_directional hu (Pi.single j 1)) continuous_const).measurableSet
    have hpe : MeasurableSet {z : ℝ×(Fin m→ℝ) | u (e.symm z)=0 → cellGradient u (e.symm z) j=0} :=
      hp.preimage e.symm.measurable
    have hs (y : Fin m→ℝ) : ∀ᵐ t ∂volume,
        u (e.symm (t,y))=0 → cellGradient u (e.symm (t,y)) j=0 := by
      have hd (t : ℝ) := (hu.differentiable one_ne_zero (j.insertNth t y)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_insertNth j y t)
      have hdiff : Differentiable ℝ (fun t ↦ u (j.insertNth t y)) :=
        fun t ↦ (hd t).differentiableAt
      have h := deriv_zero_ae_on_level hdiff
      filter_upwards [h] with t ht
      change u (j.insertNth t y)=0 → fderiv ℝ u (j.insertNth t y) (Pi.single j 1)=0
      rw [← (hd t).deriv]
      exact ht
    have hprod : ∀ᵐ z ∂(volume.prod volume : Measure (ℝ×(Fin m→ℝ))),
        u (e.symm z)=0 → cellGradient u (e.symm z) j=0 :=
      (Measure.ae_prod_iff_ae_ae hpe).mpr ((Measure.ae_ae_comm hpe).mpr (Eventually.of_forall hs))
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) ↦ ℝ) j).quasiMeasurePreserving.ae hprod
    simpa only [e, MeasurableEquiv.symm_apply_apply] using h
  filter_upwards [ae_all_iff.mpr hj] with x hx hzero
  ext j
  exact hx j hzero

end OAI.Analysis.PDE.Variational
