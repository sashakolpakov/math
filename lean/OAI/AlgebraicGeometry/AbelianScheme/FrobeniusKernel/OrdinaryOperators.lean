import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedY
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedZ

/-! # Ordinary Operators -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The constructed complete quotients define the actual ordinary Y and Z
operators. Their Frobenius identities preserve every etale-line multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (O : D.OrdinaryKernelData j iota' hsplit labels)
variable (C0 : D.CompactKernelPrescription j iota' hsplit labels)
variable (hC0 : D.CompactKernelCondition j iota' hsplit labels O C0)
variable (hgood : D.IsGoodCompletelySplitReduction)

def Integral.Construction.SplitPELReduction.fullOrdinaryY (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) : D.OrdinaryPoint :=
  D.prescribedQuotientOrdinaryPoint j iota' hsplit labels hc O x 1
    (D.prescribedYChosen j iota' hsplit labels O C0 x L) hgood

def Integral.Construction.SplitPELReduction.fullOrdinaryZ (x : D.OrdinaryPoint) : D.OrdinaryPoint :=
  D.prescribedQuotientOrdinaryPoint j iota' hsplit labels hc O x 2
    (D.prescribedZChosen j iota' hsplit labels O C0 x) hgood

def Integral.Construction.SplitPELReduction.fullOrdinaryY_witness (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    D.PrescribedOrdinaryQuotient x q (D.prescribedFullYKernel j iota' hsplit labels O C0 x L)
      (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood x L) := by
  exact (congrArg
    (fun m : ℕ => D.PrescribedOrdinaryQuotient x m
      (D.prescribedFullYKernel j iota' hsplit labels O C0 x L)
      (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood x L))
    (pow_one q)).mp
      (D.prescribedFullOrdinaryQuotient j iota' hsplit labels hc O x 1
        (D.prescribedYChosen j iota' hsplit labels O C0 x L) hgood)

def Integral.Construction.SplitPELReduction.fullOrdinaryZ_witness (x : D.OrdinaryPoint) :
    D.PrescribedOrdinaryQuotient x (q ^ 2) (D.prescribedFullZKernel j iota' hsplit labels O C0 x)
      (D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood x) :=
  D.prescribedFullOrdinaryQuotient j iota' hsplit labels hc O x 2
    (D.prescribedZChosen j iota' hsplit labels O C0 x) hgood

theorem Integral.Construction.SplitPELReduction.fullOrdinaryY_canonical (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    D.CanonicalOrdinaryQuotient x q (D.prescribedFullYKernel j iota' hsplit labels O C0 x L)
      (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood x L) :=
  Integral.Construction.SplitPELReduction.canonicalOrdinaryQuotient_of_witness (D.fullOrdinaryY_witness j iota' hsplit labels hc O C0 hgood x L) hgood

theorem Integral.Construction.SplitPELReduction.fullOrdinaryZ_canonical (x : D.OrdinaryPoint) :
    D.CanonicalOrdinaryQuotient x (q ^ 2) (D.prescribedFullZKernel j iota' hsplit labels O C0 x)
      (D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood x) :=
  Integral.Construction.SplitPELReduction.canonicalOrdinaryQuotient_of_witness (D.fullOrdinaryZ_witness j iota' hsplit labels hc O C0 hgood x) hgood

include hC0 in
theorem Integral.Construction.SplitPELReduction.fullOrdinaryY_multiset_frobenius (x : D.OrdinaryPoint) :
    (OperatorSpecification.Construction.etaleLineMultiset (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood x)).map D.ordinaryFrobenius =
      OperatorSpecification.Construction.etaleLineMultiset (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood (D.ordinaryFrobenius x)) :=
  D.prescribedYQuotient_multiset_frobenius j iota' hsplit labels O C0 hC0
    (D.fullOrdinaryY j iota' hsplit labels hc O C0 hgood)
    (D.fullOrdinaryY_witness j iota' hsplit labels hc O C0 hgood) hgood x

include hC0 in
theorem Integral.Construction.SplitPELReduction.fullOrdinaryZ_frobenius (x : D.OrdinaryPoint) :
    D.ordinaryFrobenius (D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood x) =
      D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood (D.ordinaryFrobenius x) :=
  D.prescribedZQuotient_frobenius j iota' hsplit labels O C0 hC0
    (D.fullOrdinaryZ j iota' hsplit labels hc O C0 hgood)
    (D.fullOrdinaryZ_witness j iota' hsplit labels hc O C0 hgood) hgood x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
