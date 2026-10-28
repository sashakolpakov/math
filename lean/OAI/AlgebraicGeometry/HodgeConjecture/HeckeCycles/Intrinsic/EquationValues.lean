import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData

/-! # Equation Values -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationValues.CM.IntrinsicPoints

noncomputable section

/-! Substitute the original source and branch images in the native
specialized equation before instantiating the complete PEL model. -/

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

theorem equation_values (f : D.EndK) (x y : U ⟶ D.space)
    (Nx Ny : Multiset (U ⟶ D.space))
    (sx sy : Additive (Uk ⟶ (H).X)) (rx ry : Multiset (Additive (Uk ⟶ (H).X)))
    (hx : EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V x = sx)
    (hy : EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V y = sy)
    (hNx : Nx.map (EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V) = rx)
    (hNy : Ny.map (EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V) = ry)
    (h : EquationData.CM.IntrinsicPoints.Equation D hg j hcop res hres V f x y Nx Ny) :
    PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f)
      (sx - sy) = rx.sum - ry.sum :=
  Source.EquationImages.CM.evaluated_points
    (PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f))
    (EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V) x y Nx Ny sx sy rx ry hx hy hNx hNy h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationValues.CM.IntrinsicPoints
