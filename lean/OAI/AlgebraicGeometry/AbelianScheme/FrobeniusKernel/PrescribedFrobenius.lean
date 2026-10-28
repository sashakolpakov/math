import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotients
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedCompactKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOrdinary
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ClassifyingDataIso

/-! # Prescribed Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The exact X prescription in the full statement has a canonical full
ordinary PEL quotient, namely the independently defined Frobenius point. -/

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
variable (C0 : D.CompactKernelPrescription j iota' hsplit labels)
variable (hC0 : D.CompactKernelCondition j iota' hsplit labels O C0)
variable (x : D.OrdinaryPoint)

include hc hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedFullXKernel_frobenius (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    D.prescribedFullXKernel j iota' hsplit labels O C0 x T a ↔
      D.relativeFrobeniusKernelCondition x T a :=
  (D.prescribedFullXKernel_multiplicative j iota' hsplit labels O C0 hC0 x T a).trans
    (CanonicalOrdinary.Construction.canonicalOrdinaryPrescription_frobenius j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
      (s + 1) labels hc (CMPointsYZQuotients.Construction.l45MultiplicativeHeights (O.compact x))
      (CMPointsYZQuotients.Construction.l45EtaleHeights (O.compact x)) (O.splitting x 1) T a)

include hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedXKernel_frobeniusUniversal :
    Prescribed.Construction.PrescribedKernel
      (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
        (D.pointDatum x.val).data.polarized.abelian).hom
      (D.prescribedKernelInclusion j iota' hsplit labels hc O x 1
        (D.prescribedXChosen j iota' hsplit labels O C0 x)) := by
  let H := D.prescribedXChosen j iota' hsplit labels O C0 x
  let i := D.prescribedKernelInclusion j iota' hsplit labels hc O x 1 H
  have : IsClosedImmersion i.left := D.prescribedKernel_closed j iota' hsplit labels hc O x 1 H
  have : Mono i := Over.mono_of_mono_left _
  intro T a
  have h := (D.prescribedKernel_realizes j iota' hsplit labels hc O x 1 H T a).trans
    (D.prescribedFullXKernel_frobenius j iota' hsplit labels hc O C0 hC0 x T a)
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := h.mpr ha
    exact ⟨b, hb, fun b' hb' => (cancel_mono i).mp (hb'.trans hb.symm)⟩
  · intro ha
    exact h.mp ha.exists

def Integral.Construction.SplitPELReduction.prescribedXQuotientWitness : D.QuotientWitness (D.pointDatum x.val) q
    (D.prescribedKernelGroup j iota' hsplit labels O x 1
      (D.prescribedXChosen j iota' hsplit labels O C0 x))
    (D.prescribedKernelInclusion j iota' hsplit labels hc O x 1
      (D.prescribedXChosen j iota' hsplit labels O C0 x)) :=
  D.frobeniusQuotientWitness (D.pointDatum x.val) _ _
    (D.prescribedXKernel_frobeniusUniversal j iota' hsplit labels hc O C0 hC0 x)

def Integral.Construction.SplitPELReduction.prescribedXOrdinaryQuotient : D.PrescribedOrdinaryQuotient x q
    (D.prescribedFullXKernel j iota' hsplit labels O C0 x) (D.ordinaryFrobenius x) where
  group := D.prescribedKernelGroup j iota' hsplit labels O x 1
    (D.prescribedXChosen j iota' hsplit labels O C0 x)
  inclusion := D.prescribedKernelInclusion j iota' hsplit labels hc O x 1
    (D.prescribedXChosen j iota' hsplit labels O C0 x)
  preservesGroup := Canonical.Construction.canonicalFullKernelInclusion_isMonHom ..
  closed := D.prescribedKernel_closed j iota' hsplit labels hc O x 1 _
  finite := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x 1 _).1
  flat := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x 1 _).2.1
  finitePresentation := (D.prescribedKernel_finiteLocallyFree j iota' hsplit labels O x 1 _).2.2
  realizes := D.prescribedKernel_realizes j iota' hsplit labels hc O x 1 _
  quotient := D.prescribedXQuotientWitness j iota' hsplit labels hc O C0 hC0 x
  classifies := by
    apply D.pointClassifies_of_pointDatumIso
    change PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (D.pointDatum (D.frobeniusPoint x.val)).data
      ((D.pointDatum x.val).data.pullback D.nativeIntegralGeometricFrobenius.left)
    rw [D.nativeIntegralGeometricFrobenius_eq]
    exact (D.pointDatumFrobeniusIso x.val).symm

include hc hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedX_canonicalFrobenius (hgood : D.IsGoodCompletelySplitReduction) :
    D.CanonicalOrdinaryQuotient x q (D.prescribedFullXKernel j iota' hsplit labels O C0 x)
      (D.ordinaryFrobenius x) :=
  Integral.Construction.SplitPELReduction.canonicalOrdinaryQuotient_of_witness
    (D.prescribedXOrdinaryQuotient j iota' hsplit labels hc O C0 hC0 x) hgood

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
