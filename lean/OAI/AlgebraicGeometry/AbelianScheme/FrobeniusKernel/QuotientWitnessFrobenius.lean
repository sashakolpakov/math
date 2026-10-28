import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessUniqueness

/-! # Quotient Witness Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Compare a quotient constructed on the Frobenius source with the
actual base change of the original quotient. Equal prescribed kernels
and the multiplier determine the entire target point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {source : D.GeometricPELDatum} {m : ℕ}
variable {H : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ source.data.polarized.abelian.scheme}

theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobenius_point_eq (Q : D.QuotientWitness source m H i)
    (QF : D.QuotientWitness (source.pullback D.nativeIntegralGeometricFrobenius) m
      (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup D.nativeIntegralGeometricFrobenius.left H)
      ((Over.pullback D.nativeIntegralGeometricFrobenius.left).map i))
    (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood QF.target = D.frobeniusPoint (D.pointOfPEL hgood Q.target) :=
  (QF.point_eq (Q.pullback D.nativeIntegralGeometricFrobenius) hgood).trans
    (Q.frobenius_classifies hgood)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
