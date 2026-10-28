import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting

/-! # Counting Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingOperators.CM

noncomputable section

/-! Full quotient uniqueness identifies any canonical ordinary, étale-line,
and compact quotient operators. It transfers the Frobenius and commutation
conclusions without an additional operator-matching premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

universe u v

variable (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput) (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0})
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q) (hgood : D.IsGoodCompletelySplitReduction)
  {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E) (hactiveD : D.active = 0)
  (hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
    labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
  (hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
    D.splitCoefficients n (Ideal.Quotient.mk _ a) w = j.residueCharacter iota' (labels w) n a)
  (O : D.OrdinaryKernelData j iota' hsplit labels)
  (compactKernel : D.CompactKernelPrescription j iota' hsplit labels)
  (hCompactKernel : D.CompactKernelCondition j iota' hsplit labels O compactKernel)

include hFrobeniusKernel hCMPoints hCartierDuality hgood hactive hactiveD hlabels hcoefficients hCompactKernel in
theorem canonical_operators_frobenius
    (xOperator : D.OrdinaryPoint → D.OrdinaryPoint)
    (yQuotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
    (zOperator : D.OrdinaryPoint → D.OrdinaryPoint)
    (hX : ∀ x, D.CanonicalOrdinaryQuotient x q
      (D.prescribedFullXKernel j iota' hsplit labels O compactKernel x) (xOperator x))
    (hY : ∀ x L, D.CanonicalOrdinaryQuotient x q
      (D.prescribedFullYKernel j iota' hsplit labels O compactKernel x L) (yQuotient x L))
    (hZ : ∀ x, D.CanonicalOrdinaryQuotient x (q ^ 2)
      (D.prescribedFullZKernel j iota' hsplit labels O compactKernel x) (zOperator x)) :
    (∀ x, xOperator x = D.ordinaryFrobenius x) ∧
      (∀ x, (AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient x)).map xOperator = AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (yQuotient (xOperator x))) ∧
      (∀ x, xOperator (zOperator x) = zOperator (xOperator x)) := by
  obtain ⟨canonicalX, canonicalY, canonicalZ, hCanonicalX, hCanonicalY, hCanonicalZ, _, hF, hcomm⟩ :=
    hFrobeniusKernel hCMPoints hCartierDuality D hgood j iota' hsplit labels hactive hactiveD hlabels hcoefficients O compactKernel hCompactKernel
  have xUnique : canonicalX = xOperator := funext (fun x => (hX x).2 (canonicalX x) (hCanonicalX x).1)
  have yUnique : canonicalY = yQuotient := funext (fun x => funext (fun L => (hY x L).2 (canonicalY x L) (hCanonicalY x L).1))
  have zUnique : canonicalZ = zOperator := funext (fun x => (hZ x).2 (canonicalZ x) (hCanonicalZ x).1)
  subst canonicalX canonicalY canonicalZ
  exact ⟨hF, hcomm.1, hcomm.2⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingOperators.CM
