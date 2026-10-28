import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Active Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X

noncomputable section

/-! The independent X quotient and the actual native Frobenius have
the same full kernel. Their constructed full PEL quotient isomorphism
supplies the actual Frobenius comparison for the mixed operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison.X
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (C0 : D.CompactKernelPrescription j iota hsplit labels)
  {x y : D.OrdinaryPoint}
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) y)
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM

def canonicalXSourceActiveSplitting :=
  AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota hsplit (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum y.val).data.polarized.abelian
    (D.pointDatum x.val).data.action (D.pointDatum y.val).data.action
    (FrobeniusComparison.X.canonicalXFrobeniusComparison j hsplit labels O C0 QX hFrob) (labels (0, false))
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting y 1 0))

def canonicalXLineEquiv : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q :=
  AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (labels (0, false)) (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (canonicalXSourceActiveSplitting j hsplit labels O C0 QX hFrob)

theorem canonicalXLineEquiv_eq_targetLine (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    canonicalXLineEquiv j hsplit labels O C0 QX hFrob J =
      EquivariantFrobeniusKernel.Y.targetLine j iota hsplit (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized (D.pointDatum y.val).data.polarized
        (D.pointDatum x.val).data.action (D.pointDatum y.val).data.action
        (FrobeniusComparison.X.canonicalXFrobeniusComparison j hsplit labels O C0 QX hFrob) s labels
        (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0)) (O.splitting y 1 0) J := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X
