import OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction

/-! # Dual Frame Jacobi -/

namespace OAI.RepresentationTheory.Theta.Adelic.DualFrameJacobi

noncomputable section

/-! The actual dual Hodge change of frame agrees with the Jacobi
change of variables after conversion by the position frames. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

theorem inverse_transpose_frame_identity {I : Type} [Fintype I] [DecidableEq I]
    (D Q Q' R : Matrix I I ℂ) (h : D * Q = Q' * R) :
    Q'⁻¹ᵀ * R⁻¹ᵀ = D⁻¹ᵀ * Q⁻¹ᵀ := by
  have he := congrArg (fun M : Matrix I I ℂ => M⁻¹ᵀ) h
  simpa only [Matrix.mul_inv_rev, Matrix.transpose_mul] using he.symm

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometric_dual_frame_jacobi (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (v : BallGeometryData.FrameIndex A → ℂ) :
    ((PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).invᵀ).mulVec
      (BallGeometryData.dualFrameChange A g z v) =
    (RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (PeriodCoordinates.geometricPeriod A P z)
      (((PeriodCoordinates.geometricPositionUnit A P z).invᵀ).mulVec v) := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  have hnew : (PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).inv =
      ((PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).val)⁻¹ :=
        Matrix.coe_units_inv (PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z))
  have hold : (PeriodCoordinates.geometricPositionUnit A P z).inv =
      ((PeriodCoordinates.geometricPositionUnit A P z).val)⁻¹ := Matrix.coe_units_inv (PeriodCoordinates.geometricPositionUnit A P z)
  rw [hnew, hold]
  simp only [BallGeometryData.dualFrameChange, Matrix.mulVec_mulVec]
  exact congrArg (fun M => M.mulVec v)
    (inverse_transpose_frame_identity _ _ _ _ (CoordinateFrameAction.PeriodCovariance.geometric_denominator_frame A P g z))

end

end OAI.RepresentationTheory.Theta.Adelic.DualFrameJacobi
