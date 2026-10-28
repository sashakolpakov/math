import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation

/-! # Equation Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationPoints.CM

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

theorem raw_specialization_eq (f : D.EndK) :
    @SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization K _ _ q _ _ A H cmp
      (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres)
      (Source.LocalNeighbors.CM.rawEnd D hg j hcop f).generic = EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f :=
  EquationData.CM.IntrinsicPoints.specialization_eq D hg j hcop res hres f

def RawEquation (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource)) : Prop :=
  @Source.EquationImages.CM.Equation K _ _ q _ _ A M
    (Source.Proper.CM.integralSource_proper D hg j hcop)
    V.carrier L _ _ _ _ _ _ bR cL wL (Witt.ArithmeticBase.CM.k (q := q)) _ rho Uk eR H cmp
    (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres) _
    (redM).sourceIso ((Over.pullback br).map (AlbaneseMapCompatibility.CM.arithmeticMap D hg)) U (eT).hom
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f) x y Nx Ny

theorem raw_equation_from_native (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : SpecialEquation.CM.IntrinsicTransported.Equation D hg j hcop res hres V f x y Nx Ny) :
    RawEquation D hg j hcop res hres V f x y Nx Ny :=
  @Source.EquationImages.CM.equation_from_transported K _ _ q _ _ A M
    (Source.Proper.CM.integralSource_proper D hg j hcop)
    V.carrier L _ _ _ _ _ _ bR cL wL (Witt.ArithmeticBase.CM.k (q := q)) _ rho Uk eR H cmp
    (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres) _ (redM).sourceIso ((Over.pullback br).map (AlbaneseMapCompatibility.CM.arithmeticMap D hg)) U (eT).hom
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f) x y Nx Ny h

def rawAction (f : D.EndK) : Additive (Uk ⟶ (H).X) → Additive (Uk ⟶ (H).X) :=
  @Source.EquationImages.CM.specializedAction K _ _ q _ _ A Uk H cmp
    (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres)
    (Source.LocalNeighbors.CM.rawEnd D hg j hcop f)

theorem rawAction_eq (f : D.EndK) :
    rawAction D hg j hcop res hres f =
      ⇑(PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f)) :=
  congrArg (fun g => ⇑(PointEvaluation.CM.action H Uk g))
    (raw_specialization_eq D hg j hcop res hres f)

def RawImageEquation (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource)) : Prop :=
  Source.EquationImages.CM.ImageEquation
    (PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f))
    (EquationData.CM.IntrinsicPoints.rawImage D hg j hcop res hres V) x y Nx Ny

theorem raw_equation_normalized (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : RawEquation D hg j hcop res hres V f x y Nx Ny) :
    Source.EquationImages.CM.ImageEquation (rawAction D hg j hcop res hres f)
      (EquationData.CM.IntrinsicPoints.rawImage D hg j hcop res hres V) x y Nx Ny := h

theorem raw_image_equation (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h₀ : RawEquation D hg j hcop res hres V f x y Nx Ny) :
    RawImageEquation D hg j hcop res hres V f x y Nx Ny :=
  Source.EquationImages.CM.imageEquation_congr
    (S := U ⟶ (M).genericSource) (G := Additive (Uk ⟶ (H).X))
    (rawAction D hg j hcop res hres f)
    (PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f))
    (rawAction_eq D hg j hcop res hres f)
    (EquationData.CM.IntrinsicPoints.rawImage D hg j hcop res hres V) (EquationData.CM.IntrinsicPoints.rawImage D hg j hcop res hres V) rfl x y Nx Ny
    (raw_equation_normalized D hg j hcop res hres V f x y Nx Ny h₀)

theorem equation_from_raw_image (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : RawImageEquation D hg j hcop res hres V f x y Nx Ny) :
    EquationData.CM.IntrinsicPoints.Equation D hg j hcop res hres V f x y Nx Ny :=
  Source.EquationImages.CM.imageEquation_congr
    (PointEvaluation.CM.action H Uk (EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f)) _ rfl
    (EquationData.CM.IntrinsicPoints.rawImage D hg j hcop res hres V) (EquationData.CM.IntrinsicPoints.image D hg j hcop res hres V)
    (funext (EquationData.CM.IntrinsicPoints.rawImage_eq D hg j hcop res hres V)) x y Nx Ny h

theorem equation_from_raw (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : RawEquation D hg j hcop res hres V f x y Nx Ny) :
    EquationData.CM.IntrinsicPoints.Equation D hg j hcop res hres V f x y Nx Ny :=
  equation_from_raw_image D hg j hcop res hres V f x y Nx Ny
    (raw_image_equation D hg j hcop res hres V f x y Nx Ny h)

theorem equation_from_native (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : SpecialEquation.CM.IntrinsicTransported.Equation D hg j hcop res hres V f x y Nx Ny) :
    EquationData.CM.IntrinsicPoints.Equation D hg j hcop res hres V f x y Nx Ny :=
  equation_from_raw D hg j hcop res hres V f x y Nx Ny
    (raw_equation_from_native D hg j hcop res hres V f x y Nx Ny h)

theorem equation_from_original (f : D.EndK) (x y : U ⟶ (M).genericSource)
    (Nx Ny : Multiset (U ⟶ (M).genericSource))
    (h : Source.TestEquation.CM.PointEquation D hg U f x y Nx Ny) :
    EquationData.CM.IntrinsicPoints.Equation D hg j hcop res hres V f x y Nx Ny :=
  equation_from_native D hg j hcop res hres V f x y Nx Ny
    (SpecialEquation.CM.IntrinsicTransported.equation_from_original D hg j hcop res hres V f x y Nx Ny h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationPoints.CM
