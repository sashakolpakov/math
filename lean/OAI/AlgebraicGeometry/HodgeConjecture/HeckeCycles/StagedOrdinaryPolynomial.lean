import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllOrdinaryFormulas
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CanonicalOrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.FormulaOperators

/-! # Staged Ordinary Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StagedOrdinaryPolynomial.CM.Ordinary

noncomputable section

/-! The original raw TateComparison operators satisfy the Frobenius polynomial
once full native quotient reduction supplies the ordinary neighbor counts.
IntegralModel generation and CMPoints density detect the identity on the original
special Albanese. No ordinary action or source-image matching is assumed. -/

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
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable
  (Z : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (Y : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    Multiset (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (hg : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative
local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C
  (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM

theorem polynomialRule (f : Fin 3 → (HD).EndK) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
      (Ordinary.OperatorTransport.CM.pointOperator e Z)
      (Ordinary.OperatorTransport.CM.multisetOperator e Y)
      (fun i => act (Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry f i)) →
    ∀ (x y : Intrinsic.Detection.CM.ordinaryPoints R a), x.1 = y.1 →
      act (Ordinary.Polynomial.CM.heckePolynomialValue q
        (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
        (Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry f))
        (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) = 0 :=
  CanonicalOrdinaryPolynomial.CM.Ordinary.polynomial_annihilates_actual_ordinary_differences R a
    hgeometry.smooth (Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry f)
    (Ordinary.OperatorTransport.CM.pointOperator e Z)
    (Ordinary.OperatorTransport.CM.multisetOperator e Y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StagedOrdinaryPolynomial.CM.Ordinary
