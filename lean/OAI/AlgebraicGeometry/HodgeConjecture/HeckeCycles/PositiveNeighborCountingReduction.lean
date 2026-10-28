import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingUniformReduction

/-! # Positive Neighbor Counting Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PositiveNeighborCountingReduction.CM

noncomputable section

/-! Apply uniform neighbor counting and native reduction at an arbitrary positive
source dimension, using the constructed ordinary kernel datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM

universe u v

def fixedType {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (n : ℕ) (hs : s = n + 1) : Fin s → Bool := by
  subst s
  exact RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic.prescribedMultiplicativeType P labels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

theorem native_reduction
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q) (hgood : D.IsGoodCompletelySplitReduction)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
    (labels : (Fin s × Bool) ≃ Gal(E/ℚ)) (n : ℕ) (hs : s = n + 1)
    (hactive : labels (⟨0, by omega⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    (hactiveD : D.active = ⟨0, by omega⟩)
    (hlabels : ∀ (w : Fin s) (b : Bool), labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
    (hcoefficients : ∀ (m : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin s × Bool),
      D.splitCoefficients m (Ideal.Quotient.mk _ a) w = j.residueCharacter iota (labels w) m a)
    (hdata : Nonempty (OrdinaryKernelConstruction.CM.PositiveData.KernelDataAt D j iota hsplit labels n hs))
    (hres : RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j)
    {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
    (b : B.R →+* R) (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
    (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ) :
    ∃ (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (squaredFrobeniusQuotient : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x, (AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x)).map D.ordinaryFrobenius =
        AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient (D.ordinaryFrobenius x))) ∧
      (∀ x, D.ordinaryFrobenius (squaredFrobeniusQuotient x) = squaredFrobeniusQuotient (D.ordinaryFrobenius x)) ∧
      (let etaleQuotients := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x)
       ∀ x : D.OrdinaryPoint, Nonempty (Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val) ∧
       ∀ l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val,
         Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) ⟨0, by omega⟩
           (fixedType P labels n hs) hTorsionQuotient hbase D.ordinaryFrobenius etaleQuotients squaredFrobeniusQuotient x l) := by
  subst s
  obtain ⟨O⟩ := hdata
  obtain ⟨Yquotient, squaredFrobeniusQuotient, _, _, _, hEtaleCommutes,
      hSquareCommutes, hNativeReduction⟩ :=
    Neighbor.CountingUniformReduction.CM.native_reduction_with_fixed_type hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient
      D hgood j hsplit labels hactive hactiveD hlabels hcoefficients O hres (L := L) b ρ hbase
  exact ⟨Yquotient, squaredFrobeniusQuotient, hEtaleCommutes,
    hSquareCommutes, hNativeReduction⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PositiveNeighborCountingReduction.CM
