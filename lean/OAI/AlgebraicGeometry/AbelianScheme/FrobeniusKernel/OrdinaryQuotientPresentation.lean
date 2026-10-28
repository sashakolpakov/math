import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedPresentation

/-! # Ordinary Quotient Presentation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The exact kernel presentation carried by a full ordinary quotient witness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {x y z : D.OrdinaryPoint} {m : ℕ}
variable {kernel : ∀ (T : Over D.integralGeometricBase.left),
  (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}
variable {kernelF : ∀ (T : Over D.integralGeometricBase.left),
  (T ⟶ (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian.scheme) → Prop}
variable (Q : D.PrescribedOrdinaryQuotient x m kernel y)
def Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.kernelPresentation :
    EmbeddedPresentation.Construction.EmbeddedKernelPresentation (D.pointDatum x.val).data.polarized.abelian.scheme kernel where
  object := Q.group.X
  inclusion := Q.inclusion
  mono := by
    have : IsClosedImmersion Q.inclusion.left := Q.closed
    exact Over.mono_of_mono_left _
  realizes := Q.realizes

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
