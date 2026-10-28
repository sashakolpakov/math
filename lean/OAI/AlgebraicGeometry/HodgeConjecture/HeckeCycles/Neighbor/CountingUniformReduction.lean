import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingFrobeniusReduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CompactKernelPrescription
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniformCompactType

/-! # Counting Uniform Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingUniformReduction.CM

noncomputable section

/-! Frobenius reduction and uniform compact type supply the quotient operators
and native reduction data with the fixed original PEL compact signature.  The
compact kernels and their all-test condition are constructed from the ordinary
splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM

universe u v

variable (hNeighborCounting : Counting.CM.NeighborCountingInput)
  (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput) (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0})
  (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q) (hgood : D.IsGoodCompletelySplitReduction)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E) (hactiveD : D.active = 0)
  (hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
    labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
  (hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
    D.splitCoefficients n (Ideal.Quotient.mk _ a) w = j.residueCharacter iota (labels w) n a)
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (hres : RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  (b : B.R →+* R) (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)

local notation "compactPrescription" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CompactKernelPrescription.CM.prescription D j iota hsplit labels O

include hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hgood hactive hactiveD hlabels hcoefficients hres in
theorem native_reduction_with_fixed_type :
    ∃ (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (squaredFrobeniusQuotient : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota hsplit labels O compactPrescription x) (D.ordinaryFrobenius x)) ∧
      (∀ x A, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota hsplit labels O compactPrescription x A) (Yquotient x A)) ∧
      (∀ x, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota hsplit labels O compactPrescription x) (squaredFrobeniusQuotient x)) ∧
      (∀ x, (AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x)).map D.ordinaryFrobenius =
        AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient (D.ordinaryFrobenius x))) ∧
      (∀ x, D.ordinaryFrobenius (squaredFrobeniusQuotient x) = squaredFrobeniusQuotient (D.ordinaryFrobenius x)) ∧
      (let etaleQuotients := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x)
       ∀ x : D.OrdinaryPoint, Nonempty (Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val) ∧
       ∀ l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val,
         Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) 0
           (RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic.prescribedMultiplicativeType P labels) hTorsionQuotient hbase D.ordinaryFrobenius etaleQuotients squaredFrobeniusQuotient x l) := by
  obtain ⟨Yquotient, squaredFrobeniusQuotient, hCanonicalFrobenius, hCanonicalEtale,
      hCanonicalSquare, hEtaleCommutes, hSquareCommutes, hNativeReduction⟩ :=
    CountingFrobeniusReduction.CM.native_reduction_with_frobenius hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient
      D hgood j hsplit labels hactive hactiveD hlabels hcoefficients O compactPrescription
      (CompactKernelPrescription.CM.prescription_condition D j iota hsplit labels O)
      (R := R) (L := L) b ρ hbase
  refine ⟨Yquotient, squaredFrobeniusQuotient, hCanonicalFrobenius,
    hCanonicalEtale, hCanonicalSquare, hEtaleCommutes, hSquareCommutes, ?_⟩
  dsimp only
  intro x
  refine ⟨(hNativeReduction x).1, ?_⟩
  exact UniformCompactType.CM.reduction_with_fixed_type D j hsplit labels O hres hTorsionQuotient hbase
    D.ordinaryFrobenius squaredFrobeniusQuotient (fun y => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient y))
    (fun y => (hNativeReduction y).2) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingUniformReduction.CM
