import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedPresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryComparison

/-! # Point Presentation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Native ordinary-point Frobenius transport for arbitrary embedded kernel presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable (x : D.OrdinaryPoint)
variable (P0 : ∀ (T : Over (Spec (.of (ModuliPoint.Construction.residueClosure q)))),
  (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop)
variable (P1 : ∀ (T : Over (Spec (.of (ModuliPoint.Construction.residueClosure q)))),
  (T ⟶ (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian.scheme) → Prop)
variable (K0 : EmbeddedPresentation.Construction.EmbeddedKernelPresentation (D.pointDatum x.val).data.polarized.abelian.scheme P0)
variable (K1 : EmbeddedPresentation.Construction.EmbeddedKernelPresentation
  (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian.scheme P1)
/-- Kernel-checked specialization with its type inferred from this single application. -/
abbrev Integral.Construction.SplitPELReduction.pointKernelPresentationFrobenius :=
  EmbeddedPresentation.Construction.exists_frobeniusKernelPresentationIso (q := q)
    (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    K0 K1 (D.ordinaryPointFrobeniusAbelianComparison x).abelian

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
