import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientPeriods
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus

/-! # Siegel Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelFrames.CM

noncomputable section

/-! Actual upper and lower period-frame matrices. Holomorphic dependence,
isotropy, and positivity are derived from the constructed trace geometry. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def upperPeriodFrame (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (d : Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
    (CoordinateComparison.CM.sumCoordinates K C)) (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
    (fun j => d (places.representative j)) z

def lowerPeriodFrame (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (d : Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
    (CoordinateComparison.CM.sumCoordinates K C)) (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
    (fun j => d (places.representative j)) z

theorem period_frames_apply (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (d : Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    (C.complex (Prescribed.CM.nativePeriodFrame K B places d z v)).1 = (upperPeriodFrame K C d z).mulVec v ∧
    (C.complex (Prescribed.CM.nativePeriodFrame K B places d z v)).2 = (lowerPeriodFrame K C d z).mulVec v := by
  have he := CoordinateComparison.CM.native_complex_coordinates K C
    (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished (fun j => d (places.representative j)) z v)
  change C.complex (Prescribed.CM.nativePeriodFrame K B places d z v) = _ at he
  constructor
  · rw [he]
    exact (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame_mulVec _ _ _ _ _ _).symm
  · rw [he]
    exact (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame_mulVec _ _ _ _ _ _).symm

theorem period_frames_holomorphic (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (d : Gal(K/ℚ) → Bool) :
    DifferentiableOn ℂ (upperPeriodFrame K C d) B.domain ∧
    DifferentiableOn ℂ (lowerPeriodFrame K C d) B.domain := by
  have hv (v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
      DifferentiableOn ℂ (fun z => C.complex (Prescribed.CM.nativePeriodFrame K B places d z v)) B.domain :=
    C.complex.toContinuousLinearEquiv.differentiable.comp_differentiableOn
      (CoefficientPeriods.CM.native_frame_holomorphic K B places d v)
  constructor
  · apply differentiableOn_pi.mpr
    intro r
    apply differentiableOn_pi.mpr
    intro t
    have hc := (differentiable_apply r).comp_differentiableOn (hv (Pi.single t 1)).fst
    convert hc using 1
    funext z
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Function.comp_apply] using
      (congrFun (period_frames_apply K C d z (Pi.single t 1)).1 r).symm
  · apply differentiableOn_pi.mpr
    intro r
    apply differentiableOn_pi.mpr
    intro t
    have hc := (differentiable_apply r).comp_differentiableOn (hv (Pi.single t 1)).snd
    convert hc using 1
    funext z
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Function.comp_apply] using
      (congrFun (period_frames_apply K C d z (Pi.single t 1)).2 r).symm

theorem period_frames_positive
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (P : Lagrangians.CM.LagrangianPair K B places (fun i j => d i (places.representative j)))
    (i : Fin 2) (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (ha : C.a = P.a i) (hδ : C.delta = P.delta)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (upperPeriodFrame K C (d i) z).transpose * lowerPeriodFrame K C (d i) z =
        (lowerPeriodFrame K C (d i) z).transpose * upperPeriodFrame K C (d i) z ∧
      ∀ v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ, v ≠ 0 →
        0 < (RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.standardFramePairing ((upperPeriodFrame K C (d i) z).mulVec v)
          ((lowerPeriodFrame K C (d i) z).mulVec v)).im := by
  apply RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.positivePeriod_frame_matrices
    (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) (CoordinateComparison.CM.sumCoordinates K C))
    (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished (fun j => d i (places.representative j)) z
    (Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places)
      (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)))
  · intro u v
    simpa only [ha, hδ] using CoordinateComparison.CM.coordinate_pairing_preserved K C u v
  · exact RepresentationTheory.Hecke.RadialDilation.RealStructure.Realization.rationalCoordinates_realConj K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
      (CoordinateComparison.CM.sumCoordinates K C)
  · exact CoefficientPeriods.CM.constructed_global_frame_positive K B places _ P i z hz

def lineSiegelAt
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (P : Lagrangians.CM.LagrangianPair K B places (fun i j => d i (places.representative j)))
    (i : Fin 2) (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (ha : C.a = P.a i) (hδ : C.delta = P.delta) (z : B.Domain) :
    ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places) :=
  RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame (upperPeriodFrame K C (d i) z) (lowerPeriodFrame K C (d i) z)
    (period_frames_positive K d P i C ha hδ z z.property).1
    (period_frames_positive K d P i C ha hδ z z.property).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelFrames.CM
