import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointTransport

/-! # Prescribed Z -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotients of the independently prescribed Z kernel commute
with Frobenius, retaining the original q-plane in q-squared torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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
variable (C0 : D.CompactKernelPrescription j iota' hsplit labels)
variable (hC0 : D.CompactKernelCondition j iota' hsplit labels O C0)
variable (Z : D.OrdinaryPoint → D.OrdinaryPoint)
variable (QZ : ∀ x, D.PrescribedOrdinaryQuotient x (q ^ 2)
  (D.prescribedFullZKernel j iota' hsplit labels O C0 x) (Z x))

include QZ hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedZQuotient_frobenius (hgood : D.IsGoodCompletelySplitReduction)
    (x : D.OrdinaryPoint) : D.ordinaryFrobenius (Z x) = Z (D.ordinaryFrobenius x) := by
  exact ((QZ x).frobenius_point_eq (QZ (D.ordinaryFrobenius x))
    (D.prescribedFullZKernel_transport j iota' hsplit labels O C0 hC0 x)
    hgood).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
