import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TestEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedSourceEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Proper

/-! # Evaluated Test Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedTestEquation.CM

noncomputable section

/-! An equation on the actual evaluated number-field points specializes
on the comparison model, using the constructed test identifications and
the same extending endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "M" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.nativeSource D hg j hcop
local notation "T" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))
local notation "U" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := L) j)
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.testIso (L := L) j

local instance : IsProper (M).integralSource.hom :=
  Proper.CM.integralSource_proper D hg j hcop

def Equation (f : D.EndK) (x y : U ⟶ D.space) (Nx Ny : Multiset (U ⟶ D.space)) : Prop :=
  EvaluatedSourceEquation.CM.Equation A M V (LocalNeighbors.CM.rawEnd D hg j hcop f)
    (Local.NeighborFormula.CM.liftedNeighbor T (M).sourceIso ((e).hom ≫ x))
    (Local.NeighborFormula.CM.liftedNeighbor T (M).sourceIso ((e).hom ≫ y))
    (Nx.map ((e).hom ≫ ·)) (Ny.map ((e).hom ≫ ·))

theorem equation_from_original (f : D.EndK) (x y : U ⟶ D.space)
    (Nx Ny : Multiset (U ⟶ D.space))
    (h : TestEquation.CM.PointEquation D hg U f x y Nx Ny) :
    Equation D hg j hcop V f x y Nx Ny :=
  EvaluatedSourceEquation.CM.equation_from_local A M V (LocalNeighbors.CM.rawEnd D hg j hcop f) _ _ _ _
    (TestEquation.CM.local_equation_from_test D hg j hcop T U e f x y Nx Ny h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedTestEquation.CM
