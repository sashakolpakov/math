import OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction

/-! # Geometric Action Continuity -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricActionContinuity

noncomputable section

/-! Joint continuity of the actual geometric and real coordinate actions. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometricAction_continuous :
    Continuous (fun p : RationalSU.ArchimedeanSU F H × BallGeometryData.ComplexPhase A => BallGeometryData.geometricAction A p.1 p.2) := by
  have hc (v : Fin A.places) : Continuous (fun g => BallGeometryData.standardMatrix A g v) :=
    Units.continuous_val.comp (GeometricGroup.standardUnit_continuous A v)
  have hi (v : Fin A.places) : Continuous (fun g => (BallGeometryData.standardMatrix A g v)⁻¹) := by
    have h := Units.continuous_val.comp (GeometricGroup.standardUnit_continuous A v).inv
    simpa only [Function.comp_def, Pi.inv_apply, Matrix.coe_units_inv, GeometricGroup.standardUnit_val] using h
  apply continuous_pi
  intro v
  apply Continuous.prodMk
  · apply continuous_pi
    intro ij
    change Continuous (fun p : RationalSU.ArchimedeanSU F H × BallGeometryData.ComplexPhase A =>
      ∑ k, BallGeometryData.standardMatrix A p.1 v ij.1 k * (p.2 v).1 (k, ij.2))
    fun_prop
  · apply continuous_pi
    intro ij
    change Continuous (fun p : RationalSU.ArchimedeanSU F H × BallGeometryData.ComplexPhase A =>
      ∑ k, (BallGeometryData.standardMatrix A p.1 v)⁻¹ k ij.1 * (p.2 v).2 (k, ij.2))
    apply continuous_finsetSum
    intro k _
    apply Continuous.mul
    · exact (continuous_apply ij.1).comp ((continuous_apply k).comp ((hi v).comp continuous_fst))
    · fun_prop

theorem realCoordinateAction_complex_formula (g : RationalSU.ArchimedeanSU F H)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) (i : BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) :
    RealSymplecticAction.realCoordinateAction A P g x i =
      ((ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm
        (BallGeometryData.geometricAction A g (ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun j => (x j : ℂ)))) i).re := by
  have h := ComplexIntrinsicAction.Coordinate.complex_coordinate_action A P g (fun j => (x j : ℂ))
  rw [ComplexIntrinsicAction.Coordinate.complexifiedLinear_real] at h
  have he := congrArg (fun w => ((ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm w i).re) h
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_re, LinearEquiv.coe_coe] using he

theorem realCoordinateAction_continuous :
    Continuous (fun p : RationalSU.ArchimedeanSU F H × ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) =>
      RealSymplecticAction.realCoordinateAction A P p.1 p.2) := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun p : RationalSU.ArchimedeanSU F H × ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) =>
      (p.1, ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun j => (p.2 j : ℂ)))) := by fun_prop
  have h := Complex.continuous_re.comp ((continuous_apply i).comp
    ((ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm.continuous.comp ((geometricAction_continuous A).comp hc)))
  exact h.congr (fun p => (realCoordinateAction_complex_formula A P p.1 p.2 i).symm)

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricActionContinuity
