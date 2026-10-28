import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCompactType
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantCompact

/-! # Point Compact -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The literal compact-type choice in OrdinaryKernelData is preserved
at the original Frobenius point. No coherence of the chosen splittings
at different points or torsion levels is assumed. -/

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
variable (O : D.OrdinaryKernelData j iota' hsplit labels)

theorem Integral.Construction.SplitPELReduction.ordinaryCompact_frobenius (x : D.OrdinaryPoint) (v : Fin s) :
    O.compact (D.ordinaryFrobenius x) v = O.compact x v := by
  let xF := D.ordinaryFrobenius x
  let A0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum x.val).data.polarized.abelian
  let B0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum xF.val).data.polarized.abelian
  exact (EquivariantCompact.Construction.compactType_frobenius_equivariant j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    A0 B0
    (D.pointDatum x.val).data.action (D.pointDatum xF.val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) (labels (v.succ, false))
    (O.compact x v) (O.compact xF v) (O.splitting x 1 v.succ) (O.splitting xF 1 v.succ)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
