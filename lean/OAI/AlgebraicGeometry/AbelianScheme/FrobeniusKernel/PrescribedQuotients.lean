import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalAction

/-! # Prescribed Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Construct the actual abelian quotient, integral action and full marking
for the exact chosen subgroups occurring in the repaired FrobeniusKernel statement.
Target polarization and Lie conditions are not assumed or asserted here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

include D in
theorem Integral.Construction.SplitPELReduction.polarizationType_coprime : q.Coprime (∏ i, P.polarizationType i) :=
  (Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ

variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (O : D.OrdinaryKernelData j iota' hsplit labels)
variable (x : D.OrdinaryPoint) (n : ℕ)

def Integral.Construction.SplitPELReduction.prescribedBlockCoordinates (v : Fin (s + 1)) :
    CartierModel.Construction.CartierCoordinates (.of (ModuliPoint.Construction.residueClosure q))
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (v, false)) n) :=
  CMPointsAt.Construction.l45BlockCoordinates j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (v, false)) (O.splitting x n v)

variable (H : ∀ v : Fin (s + 1), FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
  (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (v, false)) n))

def Integral.Construction.SplitPELReduction.prescribedKernelGroup : Grp (Over D.integralGeometricBase.left) :=
  CMPointsKernels.Construction.l45FullChosenKernel j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action n (s + 1) labels
    (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

def Integral.Construction.SplitPELReduction.prescribedKernelInclusion :
    (D.prescribedKernelGroup j iota' hsplit labels O x n H).X ⟶
      (D.pointDatum x.val).data.polarized.abelian.scheme :=
  Canonical.Construction.canonicalFullKernelInclusion j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

theorem Integral.Construction.SplitPELReduction.prescribedKernel_finiteLocallyFree :
    IsFinite (D.prescribedKernelGroup j iota' hsplit labels O x n H).X.hom ∧
      Flat (D.prescribedKernelGroup j iota' hsplit labels O x n H).X.hom ∧
      LocallyOfFinitePresentation (D.prescribedKernelGroup j iota' hsplit labels O x n H).X.hom :=
  CMPointsKernels.Construction.l45FullChosenKernel_finiteLocallyFree j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action n (s + 1) labels
    (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

theorem Integral.Construction.SplitPELReduction.prescribedKernel_closed :
    IsClosedImmersion (D.prescribedKernelInclusion j iota' hsplit labels hc O x n H).left :=
  Canonical.Construction.canonicalFullKernelInclusion_closed j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

theorem Integral.Construction.SplitPELReduction.prescribedKernel_realizes (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (D.prescribedKernelGroup j iota' hsplit labels O x n H).X,
      h ≫ D.prescribedKernelInclusion j iota' hsplit labels hc O x n H = a) ↔
      Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action n (s + 1) labels H T a :=
  CanonicalPoints.Construction.canonicalFullKernel_realizes j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H T a

def Integral.Construction.SplitPELReduction.prescribedAbelianQuotient :
    GeometricQuotient.Construction.GeometricKernelQuotient (D.pointDatum x.val).data.polarized.abelian
      (D.prescribedKernelGroup j iota' hsplit labels O x n H)
      (D.prescribedKernelInclusion j iota' hsplit labels hc O x n H) :=
  Canonical.Construction.canonicalFullKernelQuotient j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

def Integral.Construction.SplitPELReduction.prescribedQuotientAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E)
    (D.prescribedAbelianQuotient j iota' hsplit labels hc O x n H).abelian :=
  CanonicalAction.Construction.canonicalFullQuotientAction j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H

def Integral.Construction.SplitPELReduction.prescribedQuotientLevel : (D.prescribedAbelianQuotient j iota' hsplit labels hc O x n H).abelian.FullLevel N :=
  Canonical.Construction.canonicalFullQuotientLevel j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (D.pointDatum x.val).rosati D.polarizationType_coprime
    n (s + 1) labels hc (D.prescribedBlockCoordinates j iota' hsplit labels O x n) H D.levelPrimeToQ

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
