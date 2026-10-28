import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

/-! # Construction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Construction

noncomputable section

/-! Exact repaired NeighborCounting with the original full prerequisites and native output. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

/-- C0*T1=X0+qY0, C0²*T2=Y0(X0 x)+q²Z0, and C0³*T3=Z0(X0 x),
for actual canonical PEL quotient families and every genuine source lift. -/
theorem ordinary_neighbor_reduction_multiplicities
    (hFrobeniusKernel : Prerequisites.FullFrobeniusKernelInput) (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0})
    (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
    {iota : E →+* K} {κ : K →+* ℂ}
    {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
    (hgood : D.IsGoodCompletelySplitReduction)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
    (hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    (hactiveD : D.active = 0)
    (hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
      labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
    (hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
      D.splitCoefficients n (Ideal.Quotient.mk _ a) w = j.residueCharacter iota (labels w) n a)
    (O : D.OrdinaryKernelData j iota hsplit labels)
    (C0 : D.CompactKernelPrescription j iota hsplit labels)
    (hC0 : D.CompactKernelCondition j iota hsplit labels O C0)
    {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
    (b : B.R →+* R) (residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
    (hbase : Lifts.ResidueCompatible D R b residueIso) :
    ∃ (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
      (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (Z0 : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota hsplit labels O C0 x) (X0 x)) ∧
      (∀ x L, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota hsplit labels O C0 x L) (Yquotient x L)) ∧
      (∀ x, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota hsplit labels O C0 x) (Z0 x)) ∧
      (let Y0 : D.OrdinaryPoint → Multiset D.OrdinaryPoint := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x);
       ∀ x : D.OrdinaryPoint, Nonempty (Lifts.IntegralLift D R b residueIso x.val) ∧
       ∀ l : Lifts.IntegralLift D R b residueIso x.val,
        Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0 (Fin.cases false (O.compact x))
          hTorsionQuotient hbase X0 Y0 Z0 x l) := by
  obtain ⟨X0, Yquotient, Z0, hX, hY, hZ, hFrob, _⟩ :=
    hFrobeniusKernel hCMPoints hCartierDuality D hgood j iota hsplit labels hactive hactiveD hlabels hcoefficients O C0 hC0
  refine ⟨X0, Yquotient, Z0, hX, hY, hZ, ?_⟩
  intro Y0 x
  refine ⟨Lifts.integralLift_exists D R b residueIso hbase x.val, ?_⟩
  intro l
  let a := ConstructedActiveEvaluation.constructActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient
  exact Reference.ParameterEq.ReferenceIntrinsicReduction.nativeReductionResult_of_activeEvaluation
    j hsplit labels O l hTorsionQuotient a (fun w => hlabels w false) C0 hC0 hgood hbase
    X0 Yquotient Z0 (Classical.choice (hX x).1) hY hZ (hFrob x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Construction
