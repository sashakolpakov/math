import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientFrobenius
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientKernelFrobenius

/-! # Prescribed Quotient Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The checked kernel isomorphism and full target comparison give the
Frobenius identity of the classified ordinary quotient points. -/

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
variable (QF : D.PrescribedOrdinaryQuotient (D.ordinaryFrobenius x) m kernelF z)

abbrev Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.frobenius_target_of_kernel_transport :=
  QF.quotient.frobenius_point_eq_of_kernel_predicate
    (source := D.pointDatum x.val) (H := Q.group) (i := Q.inclusion)
    (D.ordinaryPointPolarizedFrobeniusIso x) (D.ordinaryPointFrobeniusAbelianComparison x)
    (D.ordinaryPointFrobeniusAbelianComparison_eq x)
    kernel kernelF Q.realizes QF.realizes Q.closed QF.closed

include Q QF in
/-- Exact predicate transport determines the full ordinary quotient-point relation. -/
theorem Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.frobenius_point_eq
    (htransport : Embedded.Construction.FrobeniusKernelTransport
      (D.pointDatum x.val).data.polarized.abelian
      (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
      (D.ordinaryPointFrobeniusAbelianComparison x).abelian kernel kernelF)
    (hgood : D.IsGoodCompletelySplitReduction) : z = D.ordinaryFrobenius y := by
  exact Q.point_eq_of_frobenius_target QF hgood
    (Q.frobenius_target_of_kernel_transport QF htransport Q.quotient hgood)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
