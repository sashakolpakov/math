import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingOperators

/-! # Counting Frobenius Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingFrobeniusReduction.CM

noncomputable section

/-! Retain the finite evaluation and quotient data while identifying the
ordinary quotient operator with the independently defined Frobenius map by
canonical quotient uniqueness. -/

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
  (compactKernel : D.CompactKernelPrescription j iota hsplit labels)
  (hCompactKernel : D.CompactKernelCondition j iota hsplit labels O compactKernel)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  (b : B.R →+* R) (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)

include hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hgood hactive hactiveD hlabels hcoefficients hCompactKernel in
theorem native_reduction_with_frobenius :
    ∃ (yQuotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (zOperator : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota hsplit labels O compactKernel x) (D.ordinaryFrobenius x)) ∧
      (∀ x A, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota hsplit labels O compactKernel x A) (yQuotient x A)) ∧
      (∀ x, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota hsplit labels O compactKernel x) (zOperator x)) ∧
      (∀ x, (AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient x)).map D.ordinaryFrobenius =
        AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient (D.ordinaryFrobenius x))) ∧
      (∀ x, D.ordinaryFrobenius (zOperator x) = zOperator (D.ordinaryFrobenius x)) ∧
      (let yOperator := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient x)
       ∀ x : D.OrdinaryPoint, Nonempty (Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val) ∧
       ∀ l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val,
         Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) 0
           (Fin.cases false (O.compact x)) hTorsionQuotient hbase D.ordinaryFrobenius yOperator zOperator x l) := by
  obtain ⟨xOperator, yQuotient, zOperator, hX, hY, hZ, hred⟩ :=
    hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient D hgood j hsplit labels hactive hactiveD hlabels hcoefficients
      O compactKernel hCompactKernel (R := R) (L := L) b ρ hbase
  obtain ⟨hfrob, hYcomm, hZcomm⟩ :=
    CountingOperators.CM.canonical_operators_frobenius hFrobeniusKernel hCMPoints hCartierDuality D hgood j iota hsplit labels
      hactive hactiveD hlabels hcoefficients O compactKernel hCompactKernel xOperator yQuotient zOperator hX hY hZ
  have hXeq : xOperator = D.ordinaryFrobenius := funext hfrob
  subst xOperator
  exact ⟨yQuotient, zOperator, hX, hY, hZ, hYcomm, hZcomm, hred⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingFrobeniusReduction.CM
