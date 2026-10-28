import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrame

/-! # Theta Geometric Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaGeometricCoordinates.CM

noncomputable section

/-! AdelicTheta's geometric frame matrix gives the actual coordinates of its
period graph, with no theta transformation identity involved. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hT in
theorem graph_frame (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (t : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    T.complexPhase (Sum.elim t ((T.period z).matrix.mulVec t)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z ((T.frame z).inv.mulVec t) := by
  have h := hT.2.2.2.2.2.2.1 z ((T.frame z).inv.mulVec t)
  have hm : (T.frame z).val.mulVec ((T.frame z).inv.mulVec t) = t := by
    rw [Matrix.mulVec_mulVec, (T.frame z).val_inv, Matrix.one_mulVec]
  rwa [hm] at h

include hT in
theorem frame_coordinates (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (t : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (T.frame z).val.mulVec
      (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates A (T.complexPhase (Sum.elim t ((T.period z).matrix.mulVec t)))) = t := by
  rw [graph_frame T hT, RepresentationTheory.Theta.Adelic.GeometricFrame.geometric_coordinates_frame,
    Matrix.mulVec_mulVec, (T.frame z).val_inv, Matrix.one_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaGeometricCoordinates.CM
