import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessFrobenius
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessSourceTransport

/-! # Quotient Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotient-point Frobenius comparison through an actual source
isomorphism and an embedded-kernel square. Target compatibility is
derived from quotient uniqueness and the constructed source transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {source sourceF : D.GeometricPELDatum} {m : ℕ}
variable {H HF : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ source.data.polarized.abelian.scheme}
variable {iF : HF.X ⟶ sourceF.data.polarized.abelian.scheme}

variable (QF : D.QuotientWitness sourceF m HF iF)
variable (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
  (source.pullback D.nativeIntegralGeometricFrobenius).data sourceF.data)
variable (eH : (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup D.nativeIntegralGeometricFrobenius.left H).X ≅ HF.X)
variable (he : (Over.pullback D.nativeIntegralGeometricFrobenius.left).map i ≫
  e.polarized.abelian.hom = eH.hom ≫ iF)

def Integral.Construction.SplitPELReduction.QuotientWitness.frobeniusSourceTransport :
    D.QuotientWitness (source.pullback D.nativeIntegralGeometricFrobenius) m
      (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup D.nativeIntegralGeometricFrobenius.left H)
      ((Over.pullback D.nativeIntegralGeometricFrobenius.left).map i) :=
  QF.transportSource (source' := source.pullback D.nativeIntegralGeometricFrobenius)
    ((Over.pullback D.nativeIntegralGeometricFrobenius.left).map i) e eH he

theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobeniusSourceTransport_target :
    (QF.frobeniusSourceTransport e eH he).target = QF.target := rfl

include e eH he in
theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobenius_point_eq_of_sourceIso
    (Q : D.QuotientWitness source m H i)
    (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood QF.target = D.frobeniusPoint (D.pointOfPEL hgood Q.target) :=
  (congrArg (D.pointOfPEL hgood) (QF.frobeniusSourceTransport_target e eH he).symm).trans
    (Q.frobenius_point_eq (QF.frobeniusSourceTransport e eH he) hgood)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
