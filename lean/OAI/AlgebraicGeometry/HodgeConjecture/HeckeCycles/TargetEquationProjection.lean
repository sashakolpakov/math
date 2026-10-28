import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedTargetExtension

/-! # Target Equation Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TargetEquationProjection.CM

noncomputable section

/-! The point occurring in the actual specialized neighbor equation
has the reduction of its unique arithmetic target extension. This
connects the equation's local transport to the original proper model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} [IsProper X.hom] (a : X ⟶ G.scheme)
  (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
  (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k)
  (br : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q) ⟶ S)
  (wr : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q) ≫ t = br)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

variable (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj
    (Over.mk (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))) ⟶ (Over.pullback k).obj X)
  (l : Spec (.of V.carrier) ⟶ X.left)
  (hl : l ≫ X.hom = EvaluationBaseSquare.CM.integralBase V ≫ t)
  (hz : z.left ≫ pullback.fst X.hom k = ValuativePoints.CM.genericBase (R := V.carrier) (L := L) ≫ l)

include hl hz in
theorem point_projection_extension :
    (ArithmeticEquationPoints.CM.point G a k t w br wr V z).left ≫ pullback.fst X.hom br =
      Spec.map (CommRingCat.ofHom
        (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V))) ≫ l :=
  (ArithmeticEquationPoints.CM.point_projection G a k t w br wr V z).trans
    (ProjectedTargetExtension.CM.specialization_projection t X
      (EvaluationBaseSquare.CM.integralBase V)
      (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V))
      (EvaluatedLiftProjection.CM.evaluatedLocalPoint (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))
        (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k w X (EvaluationBaseSquare.CM.integralBase V)
        (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))
        (EvaluationBaseSquare.CM.generic_square V) z) l hl
      ((EvaluatedLiftProjection.CM.arithmetic_projection (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))
        (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k w X (EvaluationBaseSquare.CM.integralBase V)
        (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))
        (EvaluationBaseSquare.CM.generic_square V) z).trans hz))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TargetEquationProjection.CM
