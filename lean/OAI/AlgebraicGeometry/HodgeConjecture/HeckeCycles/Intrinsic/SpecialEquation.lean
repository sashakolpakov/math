import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticSourceEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedTestEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction

/-! # Special Equation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialEquation.CM

/-! The original evaluated source equation specializes on the original
arithmetic source and Albanese. Its operator is the same algebraic
specialization used in the comparison-polynomial argument. -/

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
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue
  (Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "Uk" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q))
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V
local notation "H" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "cmp" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.comparisonIso D hg j hcop res hres
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction.CM.sourceReduction D hg j hcop res hres
local notation "br" => Spec.map (CommRingCat.ofHom res)

local instance : IsProper (M).integralSource.hom :=
  Source.Proper.CM.integralSource_proper D hg j hcop
local instance : GrpObj (H).X := (H).grp
local instance : IsCommMonObj (H).X := (H).comm
local instance : IsMonHom (cmp).hom :=
  ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres

local notation "localK" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.localFieldEmbedding j)
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M

def Equation (f : D.EndK) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map localK).obj T ⟶ (M).genericSource)) : Prop :=
  @Source.EquationImages.CM.Transported.Equation K _ _ q _ _ A M
    (Source.Proper.CM.integralSource_proper D hg j hcop)
    V.carrier L _ _ _ _ _ _ bR cL wL _ _ rho Uk eR H cmp
    (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres) _ (redM).sourceIso
    ((Over.pullback br).map (AlbaneseMapCompatibility.CM.arithmeticMap D hg))
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f)
    x y Nx Ny

def transport :=
  letI : IsProper D.model.space.hom := hg.proper
  ArithmeticSourceEquation.CM.transport (K := K) (q := q)
    (jq := QadicModelMap.CM.localFieldEmbedding j) (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg)
    D.generic (QadicModelMap.CM.integralBase j D.denominator hcop)
    (QadicModelMap.CM.generic_base_compatible j D.denominator D.denominator_ne_zero hcop)
    br (QadicModelMap.CM.special_base_compatible j D.denominator hcop res hres)
    cmp (Iso.ext (AlbaneseReductionMap.CM.target_identification D hg j hcop res hres))
    bR cL wL rho Uk eR

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialEquation.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialEquation.CM.IntrinsicTransported

/-! The original evaluated source equation specializes on the original
arithmetic source and Albanese. Its operator is the same algebraic
specialization used in the comparison-polynomial argument. -/

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
local notation "Uk" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q))
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V
local notation "H" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "cmp" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.comparisonIso D hg j hcop res hres
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction.CM.sourceReduction D hg j hcop res hres
local notation "br" => Spec.map (CommRingCat.ofHom res)

local instance : IsProper (M).integralSource.hom :=
  Source.Proper.CM.integralSource_proper D hg j hcop
local instance : GrpObj (H).X := (H).grp
local instance : IsCommMonObj (H).X := (H).comm
local instance : IsMonHom (cmp).hom :=
  ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres

def Equation (f : D.EndK) (x y : U ⟶ D.space) (Nx Ny : Multiset (U ⟶ D.space)) : Prop :=
  CM.Equation D hg j hcop res hres V f
    (Local.NeighborFormula.CM.liftedNeighbor T (M).sourceIso ((eT).hom ≫ x))
    (Local.NeighborFormula.CM.liftedNeighbor T (M).sourceIso ((eT).hom ≫ y))
    (Nx.map ((eT).hom ≫ ·)) (Ny.map ((eT).hom ≫ ·))

theorem equation_from_original (f : D.EndK) (x y : U ⟶ D.space)
    (Nx Ny : Multiset (U ⟶ D.space))
    (h : Source.TestEquation.CM.PointEquation D hg U f x y Nx Ny) :
    Equation D hg j hcop res hres V f x y Nx Ny :=
  (transport D hg j hcop res hres V).down
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f) _ _ _ _
    (Source.EvaluatedTestEquation.CM.equation_from_original D hg j hcop V f x y Nx Ny h)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialEquation.CM.IntrinsicTransported

end

end OAI
