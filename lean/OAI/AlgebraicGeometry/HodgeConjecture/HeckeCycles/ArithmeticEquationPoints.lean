import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedLiftProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest

/-! # Arithmetic Equation Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints.CM

noncomputable section

/-! The points occurring literally in the specialized neighbor equation
have the arithmetic projections used in the proved lift-recovery map.
This identifies the equation's reduction convention with the original
source's proper specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM
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

local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "A" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel.model K _ _ q _ jq S g G k t w
local notation "M" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM.sourceMap K _ _ q _ jq S g G X a k t w
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM.reductionMap G a red t br wr
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "gk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q)
local notation "uk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.residueBase V
local notation "Uk" => Over.mk gk
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V

local instance : IsProper (M).integralSource.hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom t))

def point (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj (Over.mk cL) ⟶ (Over.pullback k).obj X) :
    Uk ⟶ (Over.pullback br).obj X :=
  Source.SourceSpecialEquation.CM.specialNeighbor A M bR cL wL rho Uk eR z ≫ (redM).sourceIso.hom

theorem point_projection
    (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj (Over.mk cL) ⟶ (Over.pullback k).obj X) :
    (point (G := G) (a := a) (k := k) (t := t) (w := w) (br := br) (wr := wr) (V := V) z).left ≫ pullback.fst X.hom br =
      (ValuativePoints.CM.specializePoint bR rho (PullbackSpecialization.CM.localModel t X)
        (EvaluatedLiftProjection.CM.evaluatedLocalPoint eta (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k w X
          bR cL wL z)).left ≫ pullback.fst X.hom t :=
  ReductionPointProjection.CM.reducedPoint_projection
    (r := red) (b := t) (c := br) (w := wr) (X := X) (g := gk) (u := uk)
    (wu := EvaluationResidueTest.CM.residue_square V) _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints.CM
