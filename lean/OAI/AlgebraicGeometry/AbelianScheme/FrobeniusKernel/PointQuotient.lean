import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientSource

/-! # Point Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Reduction of quotient-point Frobenius compatibility to the actual
embedded-kernel base-change square. Every target comparison is derived
from the native quotient witnesses and the original point-data isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

def Integral.Construction.SplitPELReduction.nativePointDatumFrobeniusIso (x : D.GeometricPoint) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      ((D.pointDatum x).pullback D.nativeIntegralGeometricFrobenius).data
      (D.pointDatum (D.frobeniusPoint x)).data := by
  rw [D.nativeIntegralGeometricFrobenius_eq]
  exact D.pointDatumFrobeniusIso x

variable {D} (x : D.GeometricPoint) {m : ℕ}
variable {H HF : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ (D.pointDatum x).data.polarized.abelian.scheme}
variable {iF : HF.X ⟶ (D.pointDatum (D.frobeniusPoint x)).data.polarized.abelian.scheme}

/-- A concrete isomorphism of the embedded source kernels suffices.
Polarization, action, Poincare and marking compatibility of the targets
are conclusions of the quotient construction and uniqueness theorem. -/
theorem Integral.Construction.SplitPELReduction.pointQuotient_frobenius_of_kernelIso
    (Q : D.QuotientWitness (D.pointDatum x) m H i)
    (QF : D.QuotientWitness (D.pointDatum (D.frobeniusPoint x)) m HF iF)
    (eH : (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup D.nativeIntegralGeometricFrobenius.left H).X ≅ HF.X)
    (he : (Over.pullback D.nativeIntegralGeometricFrobenius.left).map i ≫
        (D.nativePointDatumFrobeniusIso x).polarized.abelian.hom = eH.hom ≫ iF)
    (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood QF.target = D.frobeniusPoint (D.pointOfPEL hgood Q.target) :=
  QF.frobenius_point_eq_of_sourceIso (D.nativePointDatumFrobeniusIso x) eH he Q hgood

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
