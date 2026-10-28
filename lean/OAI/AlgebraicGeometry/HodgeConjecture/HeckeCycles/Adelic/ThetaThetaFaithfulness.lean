import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier

/-! # Theta Theta Faithfulness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaFaithfulness.CM

noncomputable section

/-! Equality of AdelicTheta's full theta functions determines equality of the
actual evaluated finite Schwartz functions, without claiming injectivity
of the restricted-tensor presentation. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable (F : Type) [Field F] [NumberField F] {a : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ}
  {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F a m H K} (T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)

theorem functions_eq
    (f g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (h : RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T g Z.matrix) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) f = RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) g := by
  apply (Finite.RationalPositionCoordinates.CM.equivalence F (3 * m) T.rationalPosition).symm.injective
  apply Theta.Fourier.CM.Injectivity.injective Z
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (ThetaThetaCoordinates.CM.toRational F T f) Z =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (ThetaThetaCoordinates.CM.toRational F T g) Z
  calc
    _ = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix := (funext (ThetaThetaCoordinates.CM.theta_eq F T f Z)).symm
    _ = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T g Z.matrix := h
    _ = _ := funext (ThetaThetaCoordinates.CM.theta_eq F T g Z)

theorem values_eq
    (f g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (h : RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T g Z.matrix)
    (x : Fin (3 * m) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f x = RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) g x :=
  congrFun (congrArg Subtype.val (functions_eq F T f g Z h)) x

theorem theta_iff_functions_eq
    (f g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T g Z.matrix ↔
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) f = RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) g := by
  constructor
  · exact functions_eq F T f g Z
  · intro h
    funext ξ
    apply tsum_congr
    intro x
    apply congrArg (fun c : ℂ => c * RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue Z.matrix ξ (fun i => (T.rationalPosition x i : ℝ)))
    exact congrFun (congrArg Subtype.val h) (fun i => algebraMap F _ (x i))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaFaithfulness.CM
