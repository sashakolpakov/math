import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientPolarization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientLieRanks
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointDatumTorsion

/-! # Prescribed Quotient PEL Datum -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Assemble the actual full quotient PEL datum with positivity, original
polarization type, Rosati action, full marking and all geometric Lie ranks. -/

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

abbrev Integral.Construction.SplitPELReduction.prescribedQuotient_integralLieRanks :=
  CanonicalQuotientLieRanks.Construction.canonicalFullQuotient_integralLieRanks j iota' hsplit P (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ
    (B.integralEmbedding iota) D.integralGeometricBase.hom
    ((D.isOrdinary_iff_pointDatum_count x.val).mp x.property) (D.pointDatum x.val).lieRanks

def Integral.Construction.SplitPELReduction.prescribedQuotientPELDatum : D.GeometricPELDatum where
  data := D.prescribedQuotientActionData j iota' hsplit labels hc O x n H
  rosati := D.prescribedQuotientRosati j iota' hsplit labels hc O x n H
  lieRanks := D.prescribedQuotient_integralLieRanks j iota' hsplit labels hc O x n H

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
