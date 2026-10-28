import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PositiveNeighborCountingReduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOrdinaryKernelData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientResidue
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReductionFamily

/-! # Intrinsic Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.IntrinsicReduction.CM.Intrinsic

noncomputable section

/-! Derive the actual source's full native ordinary reduction family
from the complete named inputs. Kernel splittings and the fixed compact
type are constructed from the original geometry and PEL signature. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM

universe u v

variable {E K : Type} [Field E] [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (R : M.GoodIntegralReduction q j)

def multiplicative (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ)) (a : M.Family) : Fin M.s → Bool :=
  PositiveNeighborCountingReduction.CM.fixedType (M.datum a) labels (M.s - 1)
    (PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

theorem exists_reductions
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (hgeom : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion R) (hden : Nat.Coprime q M.arithmetic.denominator) :
    ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
      ∃ hlabels : ∀ (w : Fin M.s) (b : Bool),
        labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b),
        labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
        ∀ a : M.Family,
          let D := FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
          ∃ (Y : D.OrdinaryPoint → Multiset D.OrdinaryPoint) (Z : D.OrdinaryPoint → D.OrdinaryPoint),
            Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
              ⟨0, hM.1⟩ (multiplicative M hM labels a) hTorsionQuotient Z Y ∧
            (∀ x, (Y x).map D.ordinaryFrobenius = Y (D.ordinaryFrobenius x)) ∧
            (∀ x, D.ordinaryFrobenius (Z x) = Z (D.ordinaryFrobenius x)) := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal (Witt.ArithmeticBase.CM.W (q := q))) (Witt.ArithmeticBase.CM.W (q := q)) :=
    Witt.LiftBase.CM.complete q (AlgebraicClosure (ZMod q))
  obtain ⟨labels, hlabels, hactive, hdata⟩ :=
    RestrictedOrdinaryKernelData.CM.Ordinary.exists_kernelData M hM j hsplit R hgeom
  refine ⟨labels, hlabels, hactive, fun a => ?_⟩
  let D := FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
  have hgood := AbelianScheme.FrobeniusKernel.CMPointsFixedPoint.Construction.l45NativeReduction_good M R hM hsplit labels hlabels a
  have hactiveD : D.active = ⟨0, by have h := hM.1; omega⟩ :=
    congrArg Prod.fst ((congrArg labels.symm hactive.symm).trans (labels.symm_apply_apply _))
  obtain ⟨Y, Z, hY, hZ, hred⟩ := PositiveNeighborCountingReduction.CM.native_reduction
    hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient D hgood
    (Source.RestrictedPlace.CM.choice M j) (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
    labels (M.s - 1) (PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM) hactive hactiveD hlabels
    (Source.RestrictedPlace.CM.reduction_coefficients M j hM hsplit R labels hlabels a)
    (hdata a) (Source.CoefficientResidue.CM.coefficient_square M hM j hsplit R labels hlabels a hden)
    (L := Witt.ArithmeticBase.CM.Generic.F q) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q))
    (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden)
  refine ⟨fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Y x), Z, ?_, hY, hZ⟩
  intro x l
  exact (hred x).2 l

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.IntrinsicReduction.CM.Intrinsic
