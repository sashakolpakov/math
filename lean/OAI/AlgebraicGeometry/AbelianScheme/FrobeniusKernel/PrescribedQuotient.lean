import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientPELDatum
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientOrdinaryPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientUniqueness

/-! # Prescribed Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The actual full PEL quotient yields an ordinary moduli point and
the exact finite-flat prescribed quotient witness, unique as a moduli point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

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
variable (x : D.OrdinaryPoint) (n : ℕ)
variable (H : ∀ v : Fin (s + 1), FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
  (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (v, false)) n))

def Integral.Construction.SplitPELReduction.prescribedFullQuotientWitness : D.QuotientWitness (D.pointDatum x.val) (q ^ n)
    (D.prescribedKernelGroup j iota' hsplit labels O x n H)
    (D.prescribedKernelInclusion j iota' hsplit labels hc O x n H) where
  target := D.prescribedQuotientPELDatum j iota' hsplit labels hc O x n H
  isogeny := Canonical.Construction.canonicalFullQuotientIsogeny j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H
  kernel := (D.prescribedAbelianQuotient j iota' hsplit labels hc O x n H).kernel
  polarization := D.prescribedQuotientPolarized_pullback j iota' hsplit labels hc O x n H
  action a := (D.prescribedQuotientAction_intertwines j iota' hsplit labels hc O x n H a).symm
  marking := D.prescribedQuotientLevel_transports j iota' hsplit labels hc O x n H

variable (hgood : D.IsGoodCompletelySplitReduction)

def Integral.Construction.SplitPELReduction.prescribedQuotientOrdinaryPoint : D.OrdinaryPoint :=
  (D.prescribedFullQuotientWitness j iota' hsplit labels hc O x n H).ordinaryPoint hgood x.property

def Integral.Construction.SplitPELReduction.prescribedFullOrdinaryQuotient : D.PrescribedOrdinaryQuotient x (q ^ n)
    (Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action n (s + 1) labels H)
    (D.prescribedQuotientOrdinaryPoint j iota' hsplit labels hc O x n H hgood) where
  group := D.prescribedKernelGroup j iota' hsplit labels O x n H
  inclusion := D.prescribedKernelInclusion j iota' hsplit labels hc O x n H
  preservesGroup := Canonical.Construction.canonicalFullKernelInclusion_isMonHom ..
  closed := D.prescribedKernel_closed j iota' hsplit labels hc O x n H
  finite := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x n H).1
  flat := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x n H).2.1
  finitePresentation := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x n H).2.2
  realizes := D.prescribedKernel_realizes j iota' hsplit labels hc O x n H
  quotient := D.prescribedFullQuotientWitness j iota' hsplit labels hc O x n H
  classifies := D.pointOfPEL_classifies hgood _

theorem Integral.Construction.SplitPELReduction.prescribedFullQuotient_canonical : D.CanonicalOrdinaryQuotient x (q ^ n)
    (Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action n (s + 1) labels H)
    (D.prescribedQuotientOrdinaryPoint j iota' hsplit labels hc O x n H hgood) :=
  Integral.Construction.SplitPELReduction.canonicalOrdinaryQuotient_of_witness
    (D.prescribedFullOrdinaryQuotient j iota' hsplit labels hc O x n H hgood) hgood

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
