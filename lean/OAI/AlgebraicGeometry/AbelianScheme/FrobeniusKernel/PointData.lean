import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Point Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Actual PEL data at geometric moduli points and its comparison with the
independently defined Frobenius point. Polarization, Poincare bundle,
integral action, Lie condition and the full marking are retained.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

/-- The full datum at a point is pulled back from the actual integral
universal family, including its Rosati and Lie conditions. -/
def Integral.Construction.SplitPELReduction.pointDatum (x : D.GeometricPoint) : D.GeometricPELDatum :=
  D.integral.universal.pullback (D.geometricPointIntegralEquiv x)

def Integral.Construction.SplitPELReduction.integralGeometricFrobenius : D.integralGeometricBase ⟶ D.integralGeometricBase :=
  (Over.map D.specialBase).map (ModuliPoint.Construction.geometricBaseFrobenius q).hom

theorem Integral.Construction.SplitPELReduction.geometricPointIntegralEquiv_frobenius (x : D.GeometricPoint) :
    D.geometricPointIntegralEquiv (D.frobeniusPoint x) =
      D.integralGeometricFrobenius ≫ D.geometricPointIntegralEquiv x := by
  apply Over.OverMorphism.ext
  rfl

/-- Frobenius on geometric points agrees with pullback of every part of
the polarized and marked integral-action datum. -/
def Integral.Construction.SplitPELReduction.pointDatumFrobeniusIso (x : D.GeometricPoint) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      ((D.pointDatum x).data.pullback D.integralGeometricFrobenius.left)
      (D.pointDatum (D.frobeniusPoint x)).data := by
  have h : (D.geometricPointIntegralEquiv (D.frobeniusPoint x)).left =
      D.integralGeometricFrobenius.left ≫ (D.geometricPointIntegralEquiv x).left :=
    congrArg Over.Hom.left (D.geometricPointIntegralEquiv_frobenius x)
  change PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    ((D.integral.universal.data.pullback (D.geometricPointIntegralEquiv x).left).pullback
      D.integralGeometricFrobenius.left)
    (D.integral.universal.data.pullback (D.geometricPointIntegralEquiv (D.frobeniusPoint x)).left)
  rw [h]
  exact PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp D.integral.universal.data
    (D.geometricPointIntegralEquiv x).left D.integralGeometricFrobenius.left

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
