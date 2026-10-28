import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDuality

/-! # Prerequisites -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

noncomputable section

/-! The complete FrobeniusKernel statement as a conditional graph input. This is
its full quantified existence, canonicality, Frobenius-kernel and operator
proposition at ac79b0e495026f000381987ba0731b817641e8ad. The unfinished statement theorem is never imported or used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def FullFrobeniusKernelInput : Prop :=
  ∀ (_hL45 : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (_hE56 : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0})
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
    {iota : E →+* K} {κ : K →+* ℂ}
    {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
    (_hgood : D.IsGoodCompletelySplitReduction)
    {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K')
    (hsplit : j.HasSplitCoordinates iota')
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
    (_hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    (_hactiveD : D.active = 0)
    (_hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
      labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
    (_hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
      D.splitCoefficients n (Ideal.Quotient.mk _ a) w =
        j.residueCharacter iota' (labels w) n a)
    (O : D.OrdinaryKernelData j iota' hsplit labels)
    (C0 : D.CompactKernelPrescription j iota' hsplit labels)
    (_hC0 : D.CompactKernelCondition j iota' hsplit labels O C0),
    ∃ (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
      (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (Z0 : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x : D.OrdinaryPoint, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota' hsplit labels O C0 x) (X0 x)) ∧
      (∀ (x : D.OrdinaryPoint) (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q), D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota' hsplit labels O C0 x L) (Yquotient x L)) ∧
      (∀ x : D.OrdinaryPoint, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota' hsplit labels O C0 x) (Z0 x)) ∧
      (∀ (x : D.OrdinaryPoint) (T : Over D.integralGeometricBase.left)
        (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
        D.prescribedFullXKernel j iota' hsplit labels O C0 x T a ↔
          D.relativeFrobeniusKernelCondition x T a) ∧
      (∀ x : D.OrdinaryPoint, X0 x = D.ordinaryFrobenius x) ∧
      (let Y0 : D.OrdinaryPoint → Multiset D.OrdinaryPoint := fun x => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x);
        (∀ x : D.OrdinaryPoint, (Y0 x).map X0 = Y0 (X0 x)) ∧
          ∀ x : D.OrdinaryPoint, X0 (Z0 x) = Z0 (X0 x))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
