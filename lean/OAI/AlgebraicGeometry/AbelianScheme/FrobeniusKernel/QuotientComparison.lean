import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientSource
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport

/-! # Quotient Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotient-point Frobenius comparison using a supplied abelian
component whose equality with the full polarized comparison is proved. -/

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
  (source.data.pullback
    (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))))
  sourceF.data)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso
  (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) (ModuliPoint.Construction.residueClosure q) source.data.polarized.abelian)
  sourceF.data.polarized.abelian
  (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) (ModuliPoint.Construction.residueClosure q) source.data.polarized.abelian source.data.action)
  sourceF.data.action)
variable (hc : c = PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison source.data sourceF.data
  (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))) e)
variable (eH : (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))) H).X ≅ HF.X)
variable (he : (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))).map i ≫
  c.abelian.hom = eH.hom ≫ iF)

include hc he in
theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobenius_point_eq_of_comparison
    (Q : D.QuotientWitness source m H i) (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood QF.target = D.frobeniusPoint (D.pointOfPEL hgood Q.target) := by
  subst c
  exact QF.frobenius_point_eq_of_sourceIso e eH he Q hgood

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
