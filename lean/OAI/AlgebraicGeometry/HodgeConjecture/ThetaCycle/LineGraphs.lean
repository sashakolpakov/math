import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelFrames

/-! # Line Graphs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LineGraphs.CM

noncomputable section

/-! The positive frame gives exactly the graph prescribed in HeckeCycles. The
adapted graph determinant is the inverse lower-frame determinant. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (P : Lagrangians.CM.LagrangianPair K B places (fun i j => d i (places.representative j)))
  (i : Fin 2) (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (ha : C.a = P.a i) (hδ : C.delta = P.delta)

include P ha hδ in
theorem lower_period_det_ne_zero (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (SiegelFrames.CM.lowerPeriodFrame K C (d i) z).det ≠ 0 :=
  RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.positive_frame_lower_det _ _ (SiegelFrames.CM.period_frames_positive K d P i C ha hδ z hz).2

theorem graph_native_frame (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    HeckeCycles.GeometricSource.CM.graphInAmbient K C (SiegelFrames.CM.lineSiegelAt K d P i C ha hδ z) x =
      Prescribed.CM.nativePeriodFrame K B places (d i) z ((SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹.mulVec x) := by
  apply C.complex.injective
  change C.complex (C.complex.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · change (SiegelFrames.CM.upperPeriodFrame K C (d i) z * (SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹).mulVec x = _
    rw [(SiegelFrames.CM.period_frames_apply K C (d i) z _).1, Matrix.mulVec_mulVec]
  · change x = _
    rw [(SiegelFrames.CM.period_frames_apply K C (d i) z _).2, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
        (lower_period_det_ne_zero K d P i C ha hδ z z.property)), Matrix.one_mulVec]

theorem line_siegel_prescribed (z : B.Domain) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    HeckeCycles.GeometricSource.CM.prescribed K B places (d i) z w ↔
      (C.complex w).1 = (SiegelFrames.CM.lineSiegelAt K d P i C ha hδ z).matrix.mulVec (C.complex w).2 := by
  rw [← CoefficientPeriods.CM.native_frame_range K B places (d i) z w]
  constructor
  · rintro ⟨v, rfl⟩
    rw [(SiegelFrames.CM.period_frames_apply K C (d i) z v).1, (SiegelFrames.CM.period_frames_apply K C (d i) z v).2,
      Matrix.mulVec_mulVec]
    exact congrArg (fun A => A.mulVec v)
      (RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame_columns _ _ _ _).symm
  · intro hw
    refine ⟨(SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹.mulVec (C.complex w).2, ?_⟩
    rw [← graph_native_frame K d P i C ha hδ]
    apply C.complex.injective
    change C.complex (C.complex.symm _) = C.complex w
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext hw.symm rfl

theorem adapted_graph_eq_inverse (z : B.Domain) :
    (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)).comp
        (HeckeCycles.GeometricSource.CM.graphInAmbient K C (SiegelFrames.CM.lineSiegelAt K d P i C ha hδ z)) =
      Matrix.toLin' (SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹ := by
  apply LinearMap.ext
  intro x
  funext j
  change HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)
    (HeckeCycles.GeometricSource.CM.graphInAmbient K C (SiegelFrames.CM.lineSiegelAt K d P i C ha hδ z) x) j = _
  rw [graph_native_frame K d P i C ha hδ, Prescribed.CM.adapted_native_frame]
  rfl

theorem adapted_graph_det (z : B.Domain) :
    LinearMap.det ((HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)).comp
        (HeckeCycles.GeometricSource.CM.graphInAmbient K C (SiegelFrames.CM.lineSiegelAt K d P i C ha hδ z))) =
      ((SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹).det := by
  rw [adapted_graph_eq_inverse K d P i C ha hδ, LinearMap.det_toLin']

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LineGraphs.CM
