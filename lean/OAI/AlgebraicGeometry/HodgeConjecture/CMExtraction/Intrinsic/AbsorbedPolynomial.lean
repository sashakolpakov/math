import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferencePolynomialTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedOperators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Action
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SpecializedPolynomial

/-! # Absorbed Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedPolynomial.Ordinary

noncomputable section

/-! Derive FrobeniusSlope's polynomial from actual NeighborCounting native reductions on
this same integral model and TateComparison action. The complete ordinary-point
formulas and their detection are proved by the imported geometric adapters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (HeckeCycles.Witt.ArithmeticBase.CM.Generic.F q) := HeckeCycles.Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable
  (Z : (HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    (HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (Y : (HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    Multiset (HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (hg : (HeckeCycles.Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (HeckeCycles.Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (HeckeCycles.Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType
  (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.distinguished (M.datum a)) multiplicative
local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C
  (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel HD hgeometry j hden

theorem native_raw_ordinary_polynomial
    (A : AbelianScheme.CentralAction.Interface.Construction.ActionData HD) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion HD hgeometry hg hIsogenyQuotient A)
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (hreduce : HeckeCycles.Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      (M.datum a).distinguished multiplicative hTorsionQuotient Z Y) :
    HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a).X)
      (fun i => op (A.TAlb (typ i))) :=
  HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.ConcreteOrdinaryPolynomial.polynomial_from_native_reductions
    M hM j hsplit R labels hlabels a hden C (M.datum a).distinguished multiplicative
    hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient ho hd (fun i => A.TAlb (typ i))
    (fun i => Action.native_c47_raw_action HD hgeometry hg hIsogenyQuotient A hA (typ i)) hreduce

theorem native_absorbed_polynomial
    (A : AbelianScheme.CentralAction.Interface.Construction.ActionData HD) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion HD hgeometry hg hIsogenyQuotient A)
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (hreduce : HeckeCycles.Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      (M.datum a).distinguished multiplicative hTorsionQuotient Z Y) :
    SpecializedPolynomialPredicate.Intrinsic.SpecializedOrdinaryPolynomial (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model HD hgeometry hg j)
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization HD hgeometry hg hIsogenyQuotient A hA j) (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke HD A multiplicative) := by
  have hp := native_raw_ordinary_polynomial M hM j hsplit R labels hlabels a hg.2.2.2.1
    C multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient A hA ho hd hreduce
  have hs := HeckeCycles.ReferencePolynomialTransport.CM.Reference.native_source_polynomial
    M j R a hg.2.2.2.1 C (fun w => j.localCharacter M.extendedEmbedding (labels w))
    hgeometry (fun i => A.TAlb (typ i)) hp
  exact SpecializedPolynomial.native_specialized_absorbed_polynomial HD hgeometry hg hIsogenyQuotient A hA j
    R.residue R.residue_compatibility multiplicative hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedPolynomial.Ordinary
