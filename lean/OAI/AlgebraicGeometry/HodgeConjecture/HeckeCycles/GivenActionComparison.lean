import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenRealization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FamilyConcreteOrdinaryFormulas
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferencePolynomialTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comparison

/-! # Given Action Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenActionComparison.CM

noncomputable section

/-! The original polynomial, crystalline comparison are constructed for a specified GeometricTheta-compatible Hecke action. Every
operator is taken from that same action; no second action is selected. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM

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

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel HD hgeometry j hden

theorem comparison_for_given_action
    (X : RepresentationTheory.Theta.Geometric.TateComparison.Action HD)
    (hX : X.IsRealization HD hgeometry hg hIsogenyQuotient)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y) :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke M.s q) := TateComparisonAction.CM.commutativeHeckeRing M.s q hElementaryDivisors
    ∃ HR : (AM).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke M.s q),
      HR.action = (EndomorphismComparison.CM.rationalEquiv (AM).variety.scheme).toAlgHom.comp X.algebraAction ∧
      (AM).bettiHecke (HD).complexEmbedding HR = (fun h => X.cohomologyAction h) ∧
      (∀ t : AbelianScheme.TateComparison.Local.IntegralType M.s,
        HR.action (X.basis t.val) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (AM).variety.scheme (X.integral t)) ∧
      Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
        (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) (fun i => op (X.integral (typ i))) ∧
      Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
        (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (AM).specialFiber.scheme)
        (fun i => Specialized.CM.Hecke.specializedHeckeAction AM HR (X.basis (typ i).val)) ∧
      Constructed.Comparison.CM.Conclusion AM j.fieldInClosure j.complexClosure j.iota HR
        (fun i => X.basis (typ i).val)  := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke M.s q) := TateComparisonAction.CM.commutativeHeckeRing M.s q hElementaryDivisors
  obtain ⟨HR, hR, hbetti, hint⟩ :=
    GivenRealization.CM.Hecke.realization HD hgeometry j hden X hg hIsogenyQuotient hX hElementaryDivisors
  have hpoly := FamilyConcreteOrdinaryFormulas.CM.ConcreteOrdinaryPolynomial.polynomial_from_native_reductions
    M hM j hsplit R labels hlabels a hden C active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient
    ho hd (fun i => X.integral (typ i)) (fun i => hX.pointPush (typ i)) hreduce
  have hspec := ReferencePolynomialTransport.CM.Reference.specialized_polynomial
    M j R a hden C (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
    HR (fun i => X.basis (typ i).val) (fun i => X.integral (typ i))
    (fun i => hint (typ i)) hpoly
  refine ⟨HR, hR, hbetti, hint, hpoly, hspec, ?_⟩
  exact Constructed.Comparison.CM.polynomial_and_purity AM j.fieldInClosure j.complexClosure j.iota HR
      hGeometricComparison (AlbaneseModel.CM.comparisonModel_place HD j) (fun i => X.basis (typ i).val) hspec

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenActionComparison.CM
