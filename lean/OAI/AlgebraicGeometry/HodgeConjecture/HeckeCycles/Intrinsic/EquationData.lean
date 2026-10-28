import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SpecialEnd

/-! # Equation Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints

noncomputable section

/-! Write the actual specialized TateComparison equation using the exact
arithmetic points already identified with the original Witt sources and
NeighborCounting targets. Its operator is the same source specialization used in
the crystalline comparison chain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "M" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.nativeSource D hg j hcop
local notation "T" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))
local notation "U" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := L) j)
local notation "eT" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.testIso (L := L) j
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue
  (Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "Uk" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V
local notation "H" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "cmp" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.comparisonIso D hg j hcop res hres
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction.CM.sourceReduction D hg j hcop res hres
local notation "br" => Spec.map (CommRingCat.ofHom res)

local instance : IsProper (M).integralSource.hom :=
  Source.Proper.CM.integralSource_proper D hg j hcop
local instance : IsMonHom (cmp).hom :=
  ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres

def point (z : U ⟶ (M).genericSource) : Uk ⟶ (Over.pullback br).obj D.model.space := by
  let : IsProper D.model.space.hom := hg.proper
  exact ArithmeticEquationPoints.CM.point (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg)
    D.generic (QadicModelMap.CM.integralBase j D.denominator hcop)
    (QadicModelMap.CM.generic_base_compatible j D.denominator D.denominator_ne_zero hcop)
    br (QadicModelMap.CM.special_base_compatible j D.denominator hcop res hres) V ((eT).hom ≫ z)

def image (z : U ⟶ (M).genericSource) : Additive (Uk ⟶ (H).X) :=
  Additive.ofMul (point D hg j hcop res hres V z ≫ (Over.pullback br).map (AlbaneseMapCompatibility.CM.arithmeticMap D hg))

def operator (f : D.EndK) :=
  Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
    (EndomorphismComparison.CM.integralEquiv (A).variety.scheme f)

def Equation (f : D.EndK) (x y : U ⟶ (M).genericSource) (Nx Ny : Multiset (U ⟶ (M).genericSource)) : Prop :=
  Source.EquationImages.CM.ImageEquation
    (PointEvaluation.CM.action H Uk (operator D hg j hcop res hres f))
    (image D hg j hcop res hres V) x y Nx Ny

def rawImage : (U ⟶ (M).genericSource) → Additive (Uk ⟶ (H).X) :=
  @Source.EquationImages.CM.image K _ _ q _ _ A M
    (Source.Proper.CM.integralSource_proper D hg j hcop)
    V.carrier L _ _ _ _ _ _ bR cL wL (Witt.ArithmeticBase.CM.k (q := q)) _ rho Uk eR H _
    (redM).sourceIso ((Over.pullback br).map (AlbaneseMapCompatibility.CM.arithmeticMap D hg)) U (eT).hom

theorem rawImage_eq (z : U ⟶ (M).genericSource) :
    rawImage D hg j hcop res hres V z = image D hg j hcop res hres V z := by
  let : IsProper D.model.space.hom := hg.proper
  exact ArithmeticGroupEquation.CM.ImageCompatibility.image_eq (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg)
    D.generic (QadicModelMap.CM.integralBase j D.denominator hcop)
    (QadicModelMap.CM.generic_base_compatible j D.denominator D.denominator_ne_zero hcop)
    br (QadicModelMap.CM.special_base_compatible j D.denominator hcop res hres) V cmp
    (AlbaneseReductionMap.CM.target_identification D hg j hcop res hres) U (eT).hom z

theorem specialization_eq (f : D.EndK) :
    (Source.SpecialEnd.CM.sourceData D hg j hcop res hres).specialization (Source.LocalNeighbors.CM.rawEnd D hg j hcop f).generic =
      operator D hg j hcop res hres f :=
  (Source.SpecialEnd.CM.sourceData_specialization_apply D hg j hcop res hres
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f).generic).trans
      (congrArg (Source.Specialization.CM.sourceSpecialization D hg j hcop res hres)
        (Source.LocalNeighbors.CM.rawEnd_algebraic_generic D hg j hcop f))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints
