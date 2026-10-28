import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointSourceData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport

/-! # Ordinary Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full polarized Frobenius comparison on ordinary points, with both
the source and target data in the literal ordinary-operator types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

theorem Integral.Construction.SplitPELReduction.ordinaryFrobenius_value (x : D.OrdinaryPoint) :
    (D.ordinaryFrobenius x).val = D.frobeniusPoint x.val := rfl

theorem Integral.Construction.SplitPELReduction.ordinaryFrobenius_data (x : D.OrdinaryPoint) :
    (D.pointDatum (D.frobeniusPoint x.val)).data =
      (D.pointDatum (D.ordinaryFrobenius x).val).data :=
  congrArg (fun y => (D.pointDatum y).data) (D.ordinaryFrobenius_value x).symm

def Integral.Construction.SplitPELReduction.ordinaryPointPolarizedFrobeniusIso (x : D.OrdinaryPoint) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      ((D.pointDatum x.val).data.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))))
      (D.pointDatum (D.ordinaryFrobenius x).val).data :=
  PolarizedDataSourceEq.Construction.polarizedActionIso_of_target_eq _ _ _ (D.ordinaryFrobenius_data x)
    (D.pointPolarizedFrobeniusIso x.val)

def Integral.Construction.SplitPELReduction.ordinaryPointFrobeniusAbelianComparison (x : D.OrdinaryPoint) : PolarizedComponents.Construction.EquivariantAbelianIso
    (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) (ModuliPoint.Construction.residueClosure q)
      (D.pointDatum x.val).data.polarized.abelian)
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) (ModuliPoint.Construction.residueClosure q)
      (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action)
    (D.pointDatum (D.ordinaryFrobenius x).val).data.action :=
  PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison (D.pointDatum x.val).data
    (D.pointDatum (D.ordinaryFrobenius x).val).data
    (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))
    (D.ordinaryPointPolarizedFrobeniusIso x)

theorem Integral.Construction.SplitPELReduction.ordinaryPointFrobeniusAbelianComparison_eq (x : D.OrdinaryPoint) :
    D.ordinaryPointFrobeniusAbelianComparison x =
      PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison (D.pointDatum x.val).data
        (D.pointDatum (D.ordinaryFrobenius x).val).data
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))
        (D.ordinaryPointPolarizedFrobeniusIso x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
