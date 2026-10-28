import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

/-! # Counting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM

noncomputable section

/-! The neighbor-counting prerequisite packages the ordinary operators,
native evaluated PEL quotient targets, complete kernels, and their
multiplicity identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

def NeighborCountingInput : Prop := ∀
    (_frobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput) (_cmPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0})
    (_cartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
    {iota : E →+* K} {κ : K →+* ℂ}
    {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
    (_hgood : D.IsGoodCompletelySplitReduction)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
    (_hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    (_hactiveD : D.active = 0)
    (_hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
      labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
    (_hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
      D.splitCoefficients n (Ideal.Quotient.mk _ a) w = j.residueCharacter iota (labels w) n a)
    (O : D.OrdinaryKernelData j iota hsplit labels)
    (compactKernel : D.CompactKernelPrescription j iota hsplit labels)
    (_hCompactKernel : D.CompactKernelCondition j iota hsplit labels O compactKernel)
    {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
    (b : B.R →+* R) (residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
    (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b residueIso),
    ∃ (xOperator : D.OrdinaryPoint → D.OrdinaryPoint)
      (yQuotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (zOperator : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota hsplit labels O compactKernel x) (xOperator x)) ∧
      (∀ x L, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota hsplit labels O compactKernel x L) (yQuotient x L)) ∧
      (∀ x, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota hsplit labels O compactKernel x) (zOperator x)) ∧
      (let yOperator : D.OrdinaryPoint → Multiset D.OrdinaryPoint := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient x);
       ∀ x : D.OrdinaryPoint, Nonempty (Isogenies.NeighborCounting.Lifts.IntegralLift D R b residueIso x.val) ∧
       ∀ l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b residueIso x.val,
        Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) 0 (Fin.cases false (O.compact x))
          hTorsionQuotient hbase xOperator yOperator zOperator x l)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM
