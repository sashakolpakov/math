import OAI.Analysis.PDE.Concentration.Input.Integrability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

/-- The closed physical cell used by Green's formula and the half-open
Fourier cell differ only on a null set, for every rotated full lattice. -/
theorem physicalSpatialCell_ae_eq_closed {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    physicalSpatialCell R =ᵐ[volume] closedPhysicalSpatialCell R := by
  let e : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d :=
    R.trans ((LinearEquiv.smulOfNeZero ℝ (OAI.Analysis.Calculus.Current.SpatialSpace d) 100 (by norm_num)).toContinuousLinearEquiv)
  have he (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : e x = spatialCellMap R x := rfl
  have hq := (PiLp.volume_preserving_ofLp (Option (Fin d))).quasiMeasurePreserving.comp
    (Measure.ContinuousLinearMap.quasiMeasurePreserving volume e.symm.toContinuousLinearMap
      e.symm.toLinearEquiv.isUnit_det'.ne_zero)
  have hraw : {q : Option (Fin d) → ℝ | ∀ i, q i ∈ Ioc 0 1} =ᵐ[volume]
      Icc (0 : Option (Fin d) → ℝ) 1 := by
    simpa [MeasureTheory.volume_pi, Set.pi, Pi.zero_apply, Pi.one_apply] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Option (Fin d) => (volume : Measure ℝ))
        (f := 0) (g := 1))
  filter_upwards [hq.ae hraw] with x hx
  apply propext
  have hleft : x ∈ physicalSpatialCell R ↔ ∀ i, (e.symm x) i ∈ Ioc 0 1 := by
    change x ∈ e '' spatialUnitCell d ↔ _
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [e.symm_apply_apply, spatialUnitCell, Set.mem_ofPred_eq] using hy
    · intro hy
      exact ⟨e.symm x, hy, e.apply_symm_apply x⟩
  have hright : x ∈ closedPhysicalSpatialCell R ↔ (e.symm x).ofLp ∈ Icc 0 1 := by
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hh : e.symm x = spatialFromCoordinates q := by
        rw [← hqx]
        exact e.symm_apply_apply _
      rw [hh]
      exact hq
    · intro hx
      refine ⟨(e.symm x).ofLp, hx, ?_⟩
      exact e.apply_symm_apply x
  exact hleft.trans ((iff_of_eq hx).trans hright.symm)

theorem integral_closedPhysicalSpatialCell {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ) :
    (∫ x in closedPhysicalSpatialCell R, f x) = ∫ x in physicalSpatialCell R, f x :=
  setIntegral_congr_set (physicalSpatialCell_ae_eq_closed R).symm

end OAI.Analysis.PDE.Concentration
