import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormalizedSplittings
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction

/-! # Field Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FieldAction.CM

noncomputable section

/-! The source's actual finite symplectic action, before restriction of
scalars, agrees with the original rational unitary action on every vector. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

def assembled : Product.CM.FiniteGroup E Q →*
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)) :=
  Finite.UnitarySymplectic.CM.assembled (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticConjugation.CM.Field.discriminant E Q) 3 1
    (Source.QuadraticForms.CM.hermitianForm E Q) (Source.QuadraticForms.CM.skewForm E Q) (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
    (Source.Characters.CM.characters E Q) (Source.GlobalFrames.CM.frames E Q)
    (Source.NormalizedSplittings.CM.splittings E Q)

def rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin 3) (Source.QuadraticConjugation.CM.Field.RealField E) :=
  RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic (Source.QuadraticForms.CM.hermitianForm E Q).val (Source.QuadraticForms.CM.skewForm E Q).val
    (Source.GlobalFrames.CM.rational E Q) (Source.TensorAction.CM.pair E Q g)

theorem rational_assembled (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    assembled E Q (Source.RationalLocal.CM.finiteHom E Q g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)))
        (rational E Q g) :=
  Finite.UnitarySymplectic.CM.assembled_rational (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticConjugation.CM.Field.discriminant E Q) 3 1
    (Source.QuadraticForms.CM.hermitianForm E Q) (Source.QuadraticForms.CM.skewForm E Q) (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
    (Source.Characters.CM.characters E Q) (Source.GlobalFrames.CM.frames E Q)
    (Source.NormalizedSplittings.CM.splittings E Q) (Source.UnitaryMatrix.CM.hom E Q g)

theorem rational_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (rational E Q g).val *ᵥ
        (Source.GlobalFrames.CM.rational E Q).coordinates (Source.TensorPairing.CM.tensorVector E Q x) =
      (Source.GlobalFrames.CM.rational E Q).coordinates
        (Source.TensorPairing.CM.tensorVector E Q (Source.ComplexAction.CM.Symplectic.rationalAction E g x)) := by
  change (LinearMap.toMatrix'
    (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction (Source.QuadraticForms.CM.hermitianForm E Q).val (Source.QuadraticForms.CM.skewForm E Q).val
      (Source.GlobalFrames.CM.rational E Q) (Source.TensorAction.CM.pair E Q g)).toLinearMap) *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  change (Source.GlobalFrames.CM.rational E Q).coordinates
    (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear (Source.QuadraticForms.CM.hermitianForm E Q).val (Source.QuadraticForms.CM.skewForm E Q).val (Source.TensorAction.CM.pair E Q g)
      ((Source.GlobalFrames.CM.rational E Q).coordinates.symm
        ((Source.GlobalFrames.CM.rational E Q).coordinates (Source.TensorPairing.CM.tensorVector E Q x)))) = _
  rw [LinearEquiv.symm_apply_apply, Source.TensorAction.CM.tensor_action]

theorem finite_rational_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (assembled E Q (Source.RationalLocal.CM.finiteHom E Q g)).val *ᵥ
      (fun i => algebraMap (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E))
        ((Source.GlobalFrames.CM.rational E Q).coordinates (Source.TensorPairing.CM.tensorVector E Q x) i)) =
      (fun i => algebraMap (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E))
        ((Source.GlobalFrames.CM.rational E Q).coordinates
          (Source.TensorPairing.CM.tensorVector E Q (Source.ComplexAction.CM.Symplectic.rationalAction E g x)) i)) := by
  rw [rational_assembled]
  funext i
  exact (RingHom.map_mulVec
    (algebraMap (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)))
    (rational E Q g).val
    ((Source.GlobalFrames.CM.rational E Q).coordinates (Source.TensorPairing.CM.tensorVector E Q x)) i).symm.trans
      (congrArg (algebraMap (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)))
        (congrFun (rational_action E Q g x) i))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FieldAction.CM
