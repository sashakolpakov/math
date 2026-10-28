import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedDataSourceEq

/-! # Point Source Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The full native point-data comparison with its source explicitly
identified as the original polarized data pulled back by scheme Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

theorem Integral.Construction.SplitPELReduction.geometricPEL_pullback_data (source : D.GeometricPELDatum)
    (f : D.integralGeometricBase ⟶ D.integralGeometricBase) :
    (source.pullback f).data = source.data.pullback f.left := rfl

theorem Integral.Construction.SplitPELReduction.nativeFrobenius_left_eq_absolute :
    D.nativeIntegralGeometricFrobenius.left =
      Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)) := rfl

theorem Integral.Construction.SplitPELReduction.nativePointFrobeniusSourceData_eq (x : D.GeometricPoint) :
    ((D.pointDatum x).pullback D.nativeIntegralGeometricFrobenius).data =
      (D.pointDatum x).data.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))) :=
  (D.geometricPEL_pullback_data (D.pointDatum x) D.nativeIntegralGeometricFrobenius).trans
    (PolarizedDataSourceEq.Construction.polarizedActionData_pullback_congr (D.pointDatum x).data D.nativeFrobenius_left_eq_absolute)

def Integral.Construction.SplitPELReduction.pointPolarizedFrobeniusIso (x : D.GeometricPoint) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      ((D.pointDatum x).data.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))))
      (D.pointDatum (D.frobeniusPoint x)).data :=
  PolarizedDataSourceEq.Construction.polarizedActionIso_of_source_eq _ _ _ (D.nativePointFrobeniusSourceData_eq x)
    (D.nativePointDatumFrobeniusIso x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
