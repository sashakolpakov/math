import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedQuotientUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotientPresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointPresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Group

/-! # Prescribed Quotient Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Exact Frobenius transport of the prescribed predicate determines
the Frobenius relation between full ordinary quotient points, regardless
of the chosen representatives of their finite kernels. -/

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
/-- The comparison of the chosen full quotient targets. -/
abbrev Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.frobenius_target_comparison :=
  QF.quotient.frobenius_point_eq_of_comparison
    (source := D.pointDatum x.val) (H := Q.group) (i := Q.inclusion)
    (D.ordinaryPointPolarizedFrobeniusIso x) (D.ordinaryPointFrobeniusAbelianComparison x)
    (D.ordinaryPointFrobeniusAbelianComparison_eq x)

/-- Classification turns equality of full quotient targets into equality
of the specified ordinary points. -/
theorem Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.point_eq_of_frobenius_target
    (hgood : D.IsGoodCompletelySplitReduction)
    (hpoint : D.pointOfPEL hgood QF.quotient.target =
      D.frobeniusPoint (D.pointOfPEL hgood Q.quotient.target)) :
    z = D.ordinaryFrobenius y := by
  apply Subtype.ext
  exact (D.pointOfPEL_eq_of_classifies hgood QF.quotient.target z.val QF.classifies).symm.trans
    (hpoint.trans ((congrArg D.frobeniusPoint
      (D.pointOfPEL_eq_of_classifies hgood Q.quotient.target y.val Q.classifies)).trans
      (D.ordinaryFrobenius_value y).symm))

/-- A comparison of the actual embedded kernels compares the classified points. -/
theorem Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.frobenius_point_of_kernelIso :
    type_of% (fun (hgood : D.IsGoodCompletelySplitReduction) eH heH =>
      Q.point_eq_of_frobenius_target QF hgood
        (Q.frobenius_target_comparison QF eH heH Q.quotient hgood)) :=
  fun (hgood : D.IsGoodCompletelySplitReduction) eH heH =>
    Q.point_eq_of_frobenius_target QF hgood
      (Q.frobenius_target_comparison QF eH heH Q.quotient hgood)

/-- The actual embedded-kernel isomorphism reconstructed from predicate transport. -/
abbrev Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.exists_frobeniusKernelIso :=
  Group.Construction.exists_frobeniusGroupKernelIso_of_closed
    (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    Q.group QF.group Q.inclusion QF.inclusion
    (D.ordinaryPointFrobeniusAbelianComparison x).abelian kernel kernelF Q.realizes QF.realizes Q.closed QF.closed

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
