import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesSubst
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesMonomial

/-! # Power Series Continuous -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesContinuous.Construction.PowerSeriesAxis

noncomputable section

/-! The first-coordinate axis projection, and its compatibility with a shear. -/

open MvPowerSeries MvPowerSeries.WithPiTopology

variable {R : Type*} [CommRing R] {n : ℕ}

def constant : MvPowerSeries (Fin n) R →ₐ[R] R where
  __ := constantCoeff
  commutes' r := by simp [MvPowerSeries.algebraMap_apply]

def axis : MvPowerSeries (Fin (n + 1)) R →ₐ[R] PowerSeries R :=
  (PowerSeries.mapAlgHom constant).comp (MvPowerSeries.finSuccEquiv R n).toAlgHom

theorem coeff_axis (f : MvPowerSeries (Fin (n + 1)) R) (m : ℕ) :
    PowerSeries.coeff m (axis f) = MvPowerSeries.coeff ((0 : Fin n →₀ ℕ).cons m) f := by
  change constantCoeff (PowerSeries.coeff m (MvPowerSeries.finSuccEquiv R n f)) = _
  exact MvPowerSeries.coeff_coeff_finSuccEquiv f

theorem continuous_axis [TopologicalSpace R] :
    Continuous (axis (R := R) (n := n)) := by
  apply continuous_pi
  intro d
  have hd : d = Finsupp.single () (d ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [hd]
  change Continuous (fun f => PowerSeries.coeff (d ()) (axis f))
  simp_rw [coeff_axis]
  exact continuous_coeff R _

theorem axis_X_zero : axis (MvPowerSeries.X (0 : Fin (n + 1)) (R := R)) = PowerSeries.X := by
  change (MvPowerSeries.finSuccEquiv R n (X 0)).map constant.toRingHom = _
  simp

theorem axis_X_succ (i : Fin n) : axis (MvPowerSeries.X i.succ (R := R)) = 0 := by
  change (MvPowerSeries.finSuccEquiv R n (X i.succ)).map constant.toRingHom = _
  simp [constant]

theorem axis_shear (a : Fin n → R) (f : MvPowerSeries (Fin (n + 1)) R) :
    axis (PowerSeriesSubst.Construction.PowerSeriesShear.equiv a f) =
      MvPowerSeries.subst (PowerSeriesMonomial.Construction.PowerSeriesLine.coordinates (Fin.cons 1 a)) f := by
  let : UniformSpace R := ⊥
  rw [PowerSeriesSubst.Construction.PowerSeriesShear.equiv_apply]
  have he : (fun i => axis (PowerSeriesSubst.Construction.PowerSeriesShear.coordinates a i)) =
      PowerSeriesMonomial.Construction.PowerSeriesLine.coordinates (Fin.cons 1 a) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [PowerSeriesSubst.Construction.PowerSeriesShear.coordinates_zero, PowerSeriesMonomial.Construction.PowerSeriesLine.coordinates, axis_X_zero]
    · simp [PowerSeriesSubst.Construction.PowerSeriesShear.coordinates_succ, PowerSeriesMonomial.Construction.PowerSeriesLine.coordinates,
        axis_X_succ, axis_X_zero]
  rw [comp_subst_apply (PowerSeriesSubst.Construction.PowerSeriesShear.hasSubst a) continuous_axis]
  have hv := PowerSeriesMonomial.Construction.PowerSeriesLine.hasSubst (Fin.cons 1 a)
  rw [← substAlgHom_apply hv, substAlgHom_eq_aeval hv]
  simp only [coe_aeval]
  exact congrArg (fun v => MvPowerSeries.eval₂ (algebraMap R (PowerSeries R)) v f) he

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesContinuous.Construction.PowerSeriesAxis
