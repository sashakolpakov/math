import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport

/-! # Prescribed Y -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotients of the independently prescribed Y kernels commute
with Frobenius, with every etale line retained in the target multiset. -/

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
variable (Y : D.OrdinaryPoint → EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
variable (QY : ∀ x L, D.PrescribedOrdinaryQuotient x q
  (D.prescribedFullYKernel j iota' hsplit labels O C0 x L) (Y x L))

include QY hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedYQuotient_frobenius (hgood : D.IsGoodCompletelySplitReduction)
    (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    D.ordinaryFrobenius (Y x L) = Y (D.ordinaryFrobenius x)
      (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L) := by
  exact ((QY x L).frobenius_point_eq
    (QY (D.ordinaryFrobenius x) (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L))
    (D.prescribedFullYKernel_transport j iota' hsplit labels O C0 hC0 x L)
    hgood).symm

include QY hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedYQuotient_multiset_frobenius (hgood : D.IsGoodCompletelySplitReduction)
    (x : D.OrdinaryPoint) :
    (OperatorSpecification.Construction.etaleLineMultiset (Y x)).map D.ordinaryFrobenius =
      OperatorSpecification.Construction.etaleLineMultiset (Y (D.ordinaryFrobenius x)) :=
  EtaleLineMultisetTransport.Construction.etaleLineMultiset_map_of_equiv (Y x) (Y (D.ordinaryFrobenius x)) D.ordinaryFrobenius
    (D.pointFrobeniusLineEquiv j iota' hsplit labels O x)
    (D.prescribedYQuotient_frobenius j iota' hsplit labels O C0 hC0 Y QY hgood x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
