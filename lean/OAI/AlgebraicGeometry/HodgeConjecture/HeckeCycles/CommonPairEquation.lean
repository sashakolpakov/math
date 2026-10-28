import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PairEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonWittEvaluation

/-! # Common Pair Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM

noncomputable section

/-! Construct the common finite field, its valuation ring, and both
field embeddings from the actual pair of NeighborCounting evaluations. The original
TateComparison pair equation then holds on this constructed arithmetic test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
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

abbrev commonField := CommonWittEvaluation.CM.field (q := q)
  (data true).field.carrier (data false).field.carrier

local notation "CF" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.commonField M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

def embedding (b : Bool) : (data b).field.carrier →ₐ[Witt.ArithmeticBase.CM.Generic.F q] (CF).carrier :=
  match b with
  | true => (CF).left
  | false => (CF).right

abbrev scalarAlgebra : Algebra (Witt.ArithmeticBase.CM.W (q := q)) (CF).carrier :=
  CommonWittEvaluation.CM.scalarAlgebra (q := q) (data true).field.carrier (data false).field.carrier

theorem scalarTower : letI := (scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data)
    IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) (CF).carrier :=
  CommonWittEvaluation.CM.scalarTower (q := q) (data true).field.carrier (data false).field.carrier

def valuationDVR : letI := (scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data)
    Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) (CF).carrier :=
  CommonWittEvaluation.CM.valuationDVR (q := q) (data true).field.carrier (data false).field.carrier

local notation "emb" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.embedding M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

def sourcePoint (b : Bool) : Over.mk (EvaluationGenericTest.CM.originalBase (L := (CF).carrier) j) ⟶ (HD).space :=
  Witt.PairEquation.CM.sourcePoint (L := (CF).carrier) M hM j hsplit R labels hlabels a hden c p lc C b

def neighbors (b : Bool) (i : Fin 3) : Multiset
    (Over.mk (EvaluationGenericTest.CM.originalBase (L := (CF).carrier) j) ⟶ (HD).space) :=
  Witt.PairEquation.CM.neighbors M hM j hsplit R labels hlabels a hden c p lc C
    active multiplicative hTorsionQuotient data emb hIsogenyQuotient b i

theorem point_equation (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    Source.TestEquation.CM.PointEquation HD hgeometry
      (Over.mk (EvaluationGenericTest.CM.originalBase (L := (CF).carrier) j)) f
      (sourcePoint M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data true)
      (sourcePoint M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data false)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data hIsogenyQuotient true i)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data hIsogenyQuotient false i) :=
  Witt.PairEquation.CM.point_equation M hM j hsplit R labels hlabels a hden c p lc C
    active multiplicative hTorsionQuotient data emb hgeometry hIsogenyQuotient i f hraw

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM
