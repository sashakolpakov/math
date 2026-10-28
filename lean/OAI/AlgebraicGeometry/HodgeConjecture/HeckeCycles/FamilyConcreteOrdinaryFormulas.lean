import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StagedOrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IndexedOperatorEquality
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CanonicalOrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.FormulaOperators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial

/-! # Family Concrete Ordinary Formulas -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.FamilyOrdinary

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

theorem formulas_for_family (f : Fin 3 → (HD).EndK)
    (h : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
      (Ordinary.OperatorTransport.CM.pointOperator e Z)
      (Ordinary.OperatorTransport.CM.multisetOperator e Y) (fun i => act (op (f i)))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
      (Ordinary.OperatorTransport.CM.pointOperator e Z)
      (Ordinary.OperatorTransport.CM.multisetOperator e Y)
      (fun i => act (Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry f i)) := by
  intro i x y hxy
  exact (congrFun (IndexedOperatorEquality.CM.action_at M j R labels a hden C hgeometry f i)
    (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y)).trans (h i x y hxy)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.FamilyOrdinary

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.IntrinsicFamily

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

include hg hIsogenyQuotient in
theorem from_native_reductions
    (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
      (Ordinary.OperatorTransport.CM.pointOperator e Z)
      (Ordinary.OperatorTransport.CM.multisetOperator e Y)
      (fun i => act (Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry f i)) :=
  FamilyOrdinary.formulas_for_family M hM j hsplit R labels hlabels a hden C Z Y hgeometry f
    (AllOrdinaryFormulas.CM.Ordinary.compact_from_native_reductions M hM j hsplit R labels hlabels a hden
      C active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient f hraw hreduce)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.IntrinsicFamily

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.ConcreteFamilyPolynomial

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

local notation "ops" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.FormulaOperators.CM.operatorFamily M j R labels a hden C hgeometry

include hg hIsogenyQuotient in
theorem annihilates
    (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y)
    (x y : Intrinsic.Detection.CM.ordinaryPoints R a) (hxy : x.1 = y.1) :
    act (Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) (ops f))
      (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) = 0 :=
  StagedOrdinaryPolynomial.CM.Ordinary.polynomialRule M hM j hsplit R labels hlabels a hden C Z Y hgeometry f
    (IntrinsicFamily.from_native_reductions M hM j hsplit R labels hlabels a hden
      C active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient f hraw hreduce) x y hxy

include hg hIsogenyQuotient in
theorem polynomial
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y) :
    Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) (ops f) = 0 :=
  Intrinsic.SpecialDetection.CM.algebraic_detection R a
    (fun c => (hgeometry.componentGeometry c).1)
    hgeometry.abelianGeometry hgeometry.generation ho hd _
    (annihilates M hM j hsplit R labels hlabels a hden
      C active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient f hraw hreduce)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.ConcreteFamilyPolynomial

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.ConcreteOrdinaryPolynomial

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

theorem detect_from_ordinary_formulas
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Z₀ : Intrinsic.Detection.CM.ordinaryPoints R a → Intrinsic.Detection.CM.ordinaryPoints R a)
    (Y₀ : Intrinsic.Detection.CM.ordinaryPoints R a → Multiset (Intrinsic.Detection.CM.ordinaryPoints R a))
    (hH : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth) Z₀ Y₀ (fun i => act (H i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H :=
  Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.polynomial_of_formulas R a
    hgeometry.smooth (fun c => (hgeometry.componentGeometry c).1)
    hgeometry.abelianGeometry hgeometry.generation ho hd H Z₀ Y₀ hH

include hg hIsogenyQuotient in
theorem polynomial_from_native_reductions
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) (fun i => op (f i)) :=
  Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.polynomial_congr q
    (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Ordinary.FormulaOperators.CM.operatorFamily_eq M j R labels a hden C hgeometry f)
    (ConcreteFamilyPolynomial.polynomial M hM j hsplit R labels hlabels a hden
      C active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient ho hd f hraw hreduce)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas.CM.ConcreteOrdinaryPolynomial

end

end OAI
