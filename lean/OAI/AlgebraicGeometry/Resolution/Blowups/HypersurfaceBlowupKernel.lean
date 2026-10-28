import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform

/-! # Hypersurface Blowup Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupKernel.Construction

noncomputable section

/-! The intrinsic hypersurface blowup has exactly the divided equation as its chart kernel. -/

universe u

variable {R : Type u} [CommRing R]

theorem ambientChartToHypersurfaceBlowup_ker (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    RingHom.ker (HypersurfaceBlowupChart.Construction.ambientChartToHypersurfaceBlowup I a z) =
      ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {z.val}) 1 a := by
  rw [Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform]
  let e := HypersurfaceBlowupChart.Construction.hypersurfaceBlowupChartEquiv I a z hc
  ext r
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change e (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) r) = 0 ↔
    Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) r = 0
  exact map_eq_zero_iff e e.injective

/-- A normal coordinate in a dual derivation frame gives the exact kernel on
every denominator chart, including the chart where the hypersurface disappears. -/
theorem framed_hypersurface_blowupChart_ker
    {k ι : Type u} [CommRing k] [Algebra k R] [IsNoetherianRing R] [Algebra ℚ R]
    [DecidableEq ι] (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0) (i j : ι) :
    RingHom.ker (HypersurfaceBlowupChart.Construction.ambientChartToHypersurfaceBlowup I (g i) (g j)) =
      ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {(g j).val}) 1 (g i) := by
  by_cases hij : i = j
  · subst j
    rw [Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform, Etale.CoefficientStep.Construction.blowupChartRatio_self,
      Ideal.span_singleton_one, Ideal.eq_top_iff_one]
    have h := HypersurfaceBlowupChart.Construction.ambientChartToHypersurfaceBlowup_ratio I (g i) (g i)
    rwa [Etale.CoefficientStep.Construction.blowupChartRatio_self] at h
  · apply ambientChartToHypersurfaceBlowup_ker
    exact NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular I (g i) (g j) ((D j).restrictScalars ℤ)
      (by simpa only [Derivation.restrictScalars_apply, ite_eq_right (Ne.symm hij)] using hD j i)
      (by simpa only [Derivation.restrictScalars_apply, ite_true] using hD j j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupKernel.Construction
