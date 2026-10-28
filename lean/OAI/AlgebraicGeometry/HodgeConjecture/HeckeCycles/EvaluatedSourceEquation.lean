import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest

/-! # Evaluated Source Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedSourceEquation.CM

noncomputable section

/-! Apply the specialization pipeline to the constructed Witt
evaluation DVR, with its proved generic and residue base diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : Source.ComparisonModel.CM.SourceMap A) [IsProper M.integralSource.hom]
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "c" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "w" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "U" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q))
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V
local notation "T" => Over.mk c
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M

def Equation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  Source.SourceSpecialEquation.CM.SpecialEquation A M bR c w rho U e f x y Nx Ny

theorem equation_from_local (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : Source.ModelNeighborFormula.CM.LocalEquation A M T f x y Nx Ny) : Equation A M V f x y Nx Ny :=
  Source.SourceSpecialEquation.CM.specialEquation_of_localEquation A M bR c w rho U e f x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedSourceEquation.CM
