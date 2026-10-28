import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData

/-! # Classifying Data Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

section

/-! Full polarized-and-marked data isomorphisms determine the moduli point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

theorem Integral.Construction.SplitPELReduction.pointClassifies_of_pointDatumIso (x : D.GeometricPoint) (A : D.GeometricPELDatum)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (D.pointDatum x).data A.data) : D.PointClassifies x A := by
  exact ⟨PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso.ofActionIso
    (e.trans (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)⟩

theorem Integral.Construction.SplitPELReduction.pointOfPEL_eq_of_pointDatumIso (hgood : D.IsGoodCompletelySplitReduction)
    (x : D.GeometricPoint) (A : D.GeometricPELDatum)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (D.pointDatum x).data A.data) : D.pointOfPEL hgood A = x :=
  D.pointOfPEL_eq_of_classifies hgood A x (D.pointClassifies_of_pointDatumIso x A e)

end

/-! Frobenius on the independently defined moduli points agrees with
classification of the full pulled-back PEL data. The result includes
the original polarization, Poincare bundle, action and full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

def Integral.Construction.SplitPELReduction.pointDatumIsoOfClassifies (x : D.GeometricPoint) (A : D.GeometricPELDatum)
    (hx : D.PointClassifies x A) : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (D.pointDatum x).data A.data :=
  (Classical.choice hx).toActionIso.trans (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId A.data)

def Integral.Construction.SplitPELReduction.pointOfPELDataIso (hgood : D.IsGoodCompletelySplitReduction) (A : D.GeometricPELDatum) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (D.pointDatum (D.pointOfPEL hgood A)).data A.data :=
  D.pointDatumIsoOfClassifies _ A (D.pointOfPEL_classifies hgood A)

def Integral.Construction.SplitPELReduction.pointOfPELFrobeniusDataIso (hgood : D.IsGoodCompletelySplitReduction)
    (A : D.GeometricPELDatum) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      (D.pointDatum (D.frobeniusPoint (D.pointOfPEL hgood A))).data
      (A.pullback D.integralGeometricFrobenius).data :=
  (D.pointDatumFrobeniusIso (D.pointOfPEL hgood A)).symm.trans
    ((D.pointOfPELDataIso hgood A).pullback D.integralGeometricFrobenius.left)

theorem Integral.Construction.SplitPELReduction.pointOfPEL_frobenius (hgood : D.IsGoodCompletelySplitReduction)
    (A : D.GeometricPELDatum) :
    D.pointOfPEL hgood (A.pullback D.integralGeometricFrobenius) =
      D.frobeniusPoint (D.pointOfPEL hgood A) :=
  D.pointOfPEL_eq_of_pointDatumIso hgood _ _ (D.pointOfPELFrobeniusDataIso hgood A)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
