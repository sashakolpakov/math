import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TargetEquationProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingTargetReduction

/-! # Counting Equation Target -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingEquationTarget.CM

noncomputable section

/-! The actual specialized equation uses NeighborCounting's original reduced target.
Both reductions are proved to be the reduction of the same unique
proper extension, with the original arithmetic and residue maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

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

  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L]
  [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)
  (z : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a) V.carrier L
    ((algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier).comp (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden)))

variable {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.arithmetic.base) (α : (M.integral a).toOver ⟶ G.scheme)

local notation "t" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.integralBase j M.arithmetic.denominator hden
local notation "w" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.generic_base_compatible j
  M.arithmetic.denominator M.arithmetic.denominator_ne_zero hden
local notation "wr" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.special_base_compatible j
  M.arithmetic.denominator hden R.residue R.residue_compatibility
local notation "localPoint" => Iso.hom (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.testIso (L := L) j) ≫
  EvaluatedTargetPoint.CM.point M hM j hsplit R labels hlabels a hden V z

def equationPoint : Over.mk (EvaluationResidueTest.CM.geometricBase (q := q)) ⟶ R.specialFiber a := by
  let : IsProper (M.integral a).toOver.hom :=
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).proper
  exact ArithmeticEquationPoints.CM.point G α M.arithmetic.generic t w R.specialBase wr V localPoint

theorem point_projection :
    (equationPoint M hM j hsplit R labels hlabels a hden V z G α).left ≫ pullback.fst (M.integral a).toOver.hom R.specialBase =
      (z.specialPoint (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V
        (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden))).left ≫
          pullback.fst (M.integral a).toOver.hom R.specialBase := by
  let : IsProper (M.integral a).toOver.hom :=
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).proper
  have hb : z.extension ≫ (M.integral a).toOver.hom =
      EvaluationBaseSquare.CM.integralBase V ≫ t :=
    z.extension_overBase.trans (EvaluationBaseSquare.CM.arithmetic_square V hden).symm
  have hp : (localPoint).left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.generic = z.map := by
    change ((EvaluationGenericTest.CM.testIso (L := L) j).hom.left ≫
      (EvaluatedTargetPoint.CM.point M hM j hsplit R labels hlabels a hden V z).left) ≫ _ = _
    rw [EvaluationGenericTest.CM.testIso_hom_left]
    exact (congrArg (fun f => f ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.generic)
      (Category.id_comp (EvaluatedTargetPoint.CM.point M hM j hsplit R labels hlabels a hden V z).left)).trans
        (EvaluatedTargetPoint.CM.point_projection M hM j hsplit R labels hlabels a hden V z)
  have h := TargetEquationProjection.CM.point_projection_extension G α M.arithmetic.generic
    t w R.specialBase wr V localPoint z.extension hb (hp.trans z.extension_generic.symm)
  have hs := CountingTargetReduction.CM.specialization_recovers_evaluated_target z
    (Witt.EvaluationDVR.CM.geometricResidueIso V)
    (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden))
  have hr := CountingTargetReduction.CM.specialization_projection z
    (Witt.EvaluationDVR.CM.geometricResidueIso V)
  exact h.trans (hr.symm.trans hs)

theorem point_eq :
    equationPoint M hM j hsplit R labels hlabels a hden V z G α =
      z.specialPoint (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V
        (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden)) :=
  ReductionPointProjection.CM.Recovery.point_eq_of_projection R.specialBase (M.integral a).toOver
    (Over.mk (EvaluationResidueTest.CM.geometricBase (q := q))) _ _
    (point_projection M hM j hsplit R labels hlabels a hden V z G α)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingEquationTarget.CM
