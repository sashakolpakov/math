import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOperators
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedFrobenius
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDuality

/-! # Construction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Construction

noncomputable section

/-! The complete FrobeniusKernel conclusion with its original repaired premises.
All target geometry and the full Lie predicates are constructed below those premises. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem ordinary_kernel_operators_and_frobenius
    (_hL45 : CMPoints.Construction.CMPointsInput) (_hE56 : CartierDuality.Construction.FullCartierDualityInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
    {iota : E →+* K} {κ : K →+* ℂ}
    {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
    (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
    (hgood : D.IsGoodCompletelySplitReduction)
    {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K')
    (hsplit : j.HasSplitCoordinates iota')
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
    (_hactive : labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    (_hactiveD : D.active = 0)
    (hlabels : ∀ (w : Fin (s + 1)) (b : Bool),
      labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
    (_hcoefficients : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (w : Fin (s + 1) × Bool),
      D.splitCoefficients n (Ideal.Quotient.mk _ a) w =
        j.residueCharacter iota' (labels w) n a)
    (O : D.OrdinaryKernelData j iota' hsplit labels)
    (C0 : D.CompactKernelPrescription j iota' hsplit labels)
    (hC0 : D.CompactKernelCondition j iota' hsplit labels O C0) :
    ∃ (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
      (Yquotient : D.OrdinaryPoint → EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
      (Z0 : D.OrdinaryPoint → D.OrdinaryPoint),
      (∀ x : D.OrdinaryPoint, D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullXKernel j iota' hsplit labels O C0 x) (X0 x)) ∧
      (∀ (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q), D.CanonicalOrdinaryQuotient x q
        (D.prescribedFullYKernel j iota' hsplit labels O C0 x L) (Yquotient x L)) ∧
      (∀ x : D.OrdinaryPoint, D.CanonicalOrdinaryQuotient x (q ^ 2)
        (D.prescribedFullZKernel j iota' hsplit labels O C0 x) (Z0 x)) ∧
      (∀ (x : D.OrdinaryPoint) (T : Over D.integralGeometricBase.left)
        (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
        D.prescribedFullXKernel j iota' hsplit labels O C0 x T a ↔
          D.relativeFrobeniusKernelCondition x T a) ∧
      (∀ x : D.OrdinaryPoint, X0 x = D.ordinaryFrobenius x) ∧
      (let Y0 : D.OrdinaryPoint → Multiset D.OrdinaryPoint := fun x => OperatorSpecification.Construction.etaleLineMultiset (Yquotient x);
        (∀ x : D.OrdinaryPoint, (Y0 x).map X0 = Y0 (X0 x)) ∧
          ∀ x : D.OrdinaryPoint, X0 (Z0 x) = Z0 (X0 x)) := by
  have hc : ∀ w, labels (w, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, false) :=
    fun w => hlabels w false
  let Y := D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood
  let Z := D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood
  refine ⟨D.ordinaryFrobenius, Y, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact D.prescribedX_canonicalFrobenius j iota' hsplit labels hc O C0 hC0 x hgood
  · intro x L
    exact D.fullOrdinaryY_canonical j iota' hsplit labels hc O C0 hgood x L
  · intro x
    exact D.fullOrdinaryZ_canonical j iota' hsplit labels hc O C0 hgood x
  · intro x T a
    exact D.prescribedFullXKernel_frobenius j iota' hsplit labels hc O C0 hC0 x T a
  · intro x
    rfl
  · exact ⟨D.fullOrdinaryY_multiset_frobenius j iota' hsplit labels hc O C0 hC0 hgood,
      D.fullOrdinaryZ_frobenius j iota' hsplit labels hc O C0 hC0 hgood⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Construction
