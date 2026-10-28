import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPELData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientDualData

/-! # Prescribed Quotient Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The prescribed ordinary kernels yield actual polarized, fully marked
quotient action data. Positivity, Rosati conjugation and the original polarization type are
proved; the PEL Lie-rank conditions remain a separate obligation. -/

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

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientPolarization :=
  CanonicalQuotientPolarization.Construction.canonicalFullQuotientPolarization j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientPolarization_nativePullback :=
  CanonicalQuotientPolarization.Construction.canonicalFullQuotientPolarization_nativePullback j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientPolarized_pullback :=
  CanonicalQuotientPELData.Construction.canonicalFullQuotientPolarized_pullback j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

def Integral.Construction.SplitPELReduction.prescribedPolarizedQuotient :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * (s + 1)) P.polarizationType N D.integralGeometricBase.left :=
  CanonicalQuotientPELData.Construction.canonicalFullQuotientPolarized j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

def Integral.Construction.SplitPELReduction.prescribedQuotientActionData :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * (s + 1)) P.polarizationType N D.integralGeometricBase.left :=
  CanonicalQuotientPELData.Construction.canonicalFullQuotientActionData j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientRosati :=
  CanonicalQuotientPELData.Construction.canonicalFullQuotientRosati j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientAction_intertwines :=
  CanonicalAction.Construction.canonicalFullQuotientAction_intertwines j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

abbrev Integral.Construction.SplitPELReduction.prescribedQuotientLevel_transports :=
  Canonical.Construction.canonicalFullQuotientLevel_transports j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
