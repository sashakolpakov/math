import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationPoints

/-! # Common Pair Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairSpecialization.CM

noncomputable section

/-! Specialize the original pair equation on the constructed common
Witt DVR. Its operator, source points and all neighbor images are the
actual arithmetic ones already identified with the original geometry. -/

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

local notation "CF" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.commonField M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "source" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.sourcePoint M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data
local notation "neighbors" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.neighbors M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data hIsogenyQuotient

def Equation (f : (HD).EndK) (i : Fin 3) : Prop := by
  letI := CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  letI := CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  exact Intrinsic.EquationData.CM.IntrinsicPoints.Equation HD hgeometry j hden R.residue R.residue_compatibility
    (CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data) f (source true) (source false) (neighbors true i) (neighbors false i)

theorem equation (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    Equation M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data hgeometry hIsogenyQuotient f i := by
  let := CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  let := CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  exact Intrinsic.EquationPoints.CM.equation_from_original HD hgeometry j hden R.residue R.residue_compatibility
    (CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data) f (source true) (source false) (neighbors true i) (neighbors false i)
    (CommonPairEquation.CM.point_equation M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hgeometry hIsogenyQuotient i f hraw)

theorem equation_explicit (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    letI := CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data
    letI := CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data
    Intrinsic.EquationData.CM.IntrinsicPoints.Equation HD hgeometry j hden R.residue R.residue_compatibility
      (CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
        active multiplicative hTorsionQuotient data) f (source true) (source false) (neighbors true i) (neighbors false i) := by
  let := CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  let := CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
    active multiplicative hTorsionQuotient data
  exact Intrinsic.EquationPoints.CM.equation_from_original HD hgeometry j hden R.residue R.residue_compatibility
    (CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
      active multiplicative hTorsionQuotient data) f (source true) (source false) (neighbors true i) (neighbors false i)
    (CommonPairEquation.CM.point_equation M hM j hsplit R labels hlabels a hden c p lc C
      active multiplicative hTorsionQuotient data hgeometry hIsogenyQuotient i f hraw)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairSpecialization.CM
