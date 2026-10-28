import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues

/-! # Common Pair Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairFormula.CM

noncomputable section

/-! The raw TateComparison equation, specialized on the constructed common DVR,
is the equation for the original source Albanese images and the entire
multisets of original NeighborCounting reduced targets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

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
  (c : Fin (M.componentCount a))
  (p : Bool → (Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c))
  (lc : ∀ b, Witt.PointLift.CM.ComponentLift R hden a c (p b))

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (data : ∀ b, Intrinsic.EvaluationData.CM.Evaluation (L := Witt.ArithmeticBase.CM.Generic.F q)
    (Source.RestrictedPlace.CM.choice M j) (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
    (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))

local notation "CF" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.commonField M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable
  (hg : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "source" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.sourcePoint M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data
local notation "neighbors" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.neighbors M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data hIsogenyQuotient

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM

local notation "alg" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "tower" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "val" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "emb" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.embedding M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

local notation "sx" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages.CM.sourceImage M j R a c p
local notation "rx" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages.CM.reducedImages M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C
  (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)

def Formula (f : (HD).EndK) (i : Fin 3) : Prop :=
  act (op f) (sx true - sx false) = (rx true i).sum - (rx false i).sum

include hg hIsogenyQuotient in
theorem formula (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    act (op f) (sx true - sx false) = (rx true i).sum - (rx false i).sum := by
  let := alg
  let := tower
  have h := CommonPairSpecialization.CM.equation_explicit M hM j hsplit R labels hlabels a hden c p lc C
    active multiplicative hTorsionQuotient data hgeometry hIsogenyQuotient i f hraw
  exact EquationValues.CM.Hecke.equation_values M j R a hden C
    (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry val f
    (source true) (source false) (neighbors true i) (neighbors false i) _ _ _ _
    (CommonPairImages.CM.source_image M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hgeometry true)
    (CommonPairImages.CM.source_image M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hgeometry false)
    (CommonPairImages.CM.neighbor_images M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hg hgeometry hIsogenyQuotient true i)
    (CommonPairImages.CM.neighbor_images M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hg hgeometry hIsogenyQuotient false i) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairFormula.CM
