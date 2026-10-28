import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ComponentIntrinsicLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EvaluationData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonCanonicalTestEquation

/-! # Pair Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PairEquation.CM

noncomputable section

/-! Derive the finite TateComparison equation for two actual native NeighborCounting
lifts in the same original component. The original evaluated branch
labels are preserved on any common field and its geometric test. -/

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
  (lc : ∀ b, PointLift.CM.ComponentLift R hden a c (p b))

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (ArithmeticBase.CM.Generic.F q) := EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (data : ∀ b, Intrinsic.EvaluationData.CM.Evaluation (L := ArithmeticBase.CM.Generic.F q)
    (Source.RestrictedPlace.CM.choice M j) (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
    (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient
    (ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  (σ : ∀ b, (data b).field.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L)
  {L' : Type} [Field L'] [IsAlgClosed L'] [Algebra (ArithmeticBase.CM.Generic.F q) L'] (τ : L →ₐ[ArithmeticBase.CM.Generic.F q] L')
  (hgeometry : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

def sourcePoint (b : Bool) : Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j) ⟶ (HD).space :=
  FieldPoint.CM.fieldPoint (L := L) (M.integral a).toOver
    (Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden
      (ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p b))
      (ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))

def branchLabels (b : Bool) (i : Fin 3) : ULift (Fin ((data b).field.count (some i))) ≃
    ((HD).correspondence (typ i)).Fiber (sourcePoint (L := L) M hM j hsplit R labels hlabels a hden c p lc C b) :=
  CanonicalLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden
    (ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p b))
    (ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b))
    C active multiplicative hTorsionQuotient (data b).field (σ b) hIsogenyQuotient i

def neighbors (b : Bool) (i : Fin 3) : Multiset (Over.mk
    (EvaluationGenericTest.CM.originalBase (L := L) j) ⟶ (HD).space) :=
  Finset.univ.val.map (fun β => ((HD).correspondence (typ i)).endpoint
    (branchLabels M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient b i β))

include τ in
theorem point_equation_over_geometric_test (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    Source.TestEquation.CM.PointEquation HD hgeometry
      (Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j)) f
      (sourcePoint (L := L) M hM j hsplit R labels hlabels a hden c p lc C true)
      (sourcePoint (L := L) M hM j hsplit R labels hlabels a hden c p lc C false)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient true i)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient false i) := by
  apply @ComparisonCanonicalTestEquation.CM.TateSource.point_equation E M.arithmetic.extension.carrier _ _ _ _ _ M.s q _
    HD hgeometry (typ i) f (Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j)) L' _ _
    (EvaluationGenericTest.CM.originalBase (L := L') j)
    (AlgebraFieldTest.CM.map (ArithmeticBase.CM.Generic.numberFieldBase j) τ)
    (AlgebraFieldTest.CM.map_epi (ArithmeticBase.CM.Generic.numberFieldBase j) τ) c
    (FieldPoint.CM.fieldPoint (L := L) ((M.components a).S c) (lc true))
    (FieldPoint.CM.fieldPoint (L := L) ((M.components a).S c) (lc false))
    _ _ _ _ _ _
    (ComponentIntrinsicLift.CM.Intrinsic.fieldPoint_component M hM j hsplit R labels hlabels a hden c (p true) (lc true) C _)
    (ComponentIntrinsicLift.CM.Intrinsic.fieldPoint_component M hM j hsplit R labels hlabels a hden c (p false) (lc false) C _)
    (branchLabels M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient true i)
    (branchLabels M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient false i)
    (CanonicalLabels.CM.Geometric.branchEquiv M hM j hsplit R labels hlabels a hden
      (ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p true))
      (ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p true) (lc true))
      C active multiplicative hTorsionQuotient (data true).field (σ true) hIsogenyQuotient τ i)
    (CanonicalLabels.CM.Geometric.branchEquiv M hM j hsplit R labels hlabels a hden
      (ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p false))
      (ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p false) (lc false))
      C active multiplicative hTorsionQuotient (data false).field (σ false) hIsogenyQuotient τ i)
    hraw

theorem point_equation (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f) :
    Source.TestEquation.CM.PointEquation HD hgeometry
      (Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j)) f
      (sourcePoint (L := L) M hM j hsplit R labels hlabels a hden c p lc C true)
      (sourcePoint (L := L) M hM j hsplit R labels hlabels a hden c p lc C false)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient true i)
      (neighbors M hM j hsplit R labels hlabels a hden c p lc C active multiplicative hTorsionQuotient data σ hIsogenyQuotient false i) := by
  exact point_equation_over_geometric_test M hM j hsplit R labels hlabels a hden c p lc C
    active multiplicative hTorsionQuotient data σ (IsScalarTower.toAlgHom (ArithmeticBase.CM.Generic.F q) L (AlgebraicClosure L))
    hgeometry hIsogenyQuotient i f hraw

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PairEquation.CM
