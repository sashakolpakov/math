import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantCompact
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Compact Type -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompactType.X

noncomputable section

/-! The independent X quotient and the actual native Frobenius have
the same full kernel. Their constructed full PEL quotient isomorphism
supplies the actual Frobenius comparison for the mixed operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

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

include QX hFrob in
theorem canonicalX_compact_type (v : Fin s) : O.compact y v = O.compact x v := by
  let A0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum x.val).data.polarized.abelian
  let B0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum y.val).data.polarized.abelian
  exact (AbelianScheme.FrobeniusKernel.EquivariantCompact.Construction.compactType_frobenius_equivariant j iota hsplit (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    A0 B0 (D.pointDatum x.val).data.action (D.pointDatum y.val).data.action
    (FrobeniusComparison.X.canonicalXFrobeniusComparison j hsplit labels O C0 QX hFrob)
    (labels (v.succ, false)) (O.compact x v) (O.compact y v)
    (O.splitting x 1 v.succ) (O.splitting y 1 v.succ)).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompactType.X
