import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ClassifyingDataIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointDatumTorsion
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedIsogenyOrdinary
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessConstruction

/-! # Quotient Ordinary Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotient witnesses over an ordinary source classify ordinary
moduli points. The target count follows from the original isogeny and
the constructed full source-data comparison, with no target assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

theorem Integral.Construction.SplitPELReduction.isOrdinary_pointOfPEL_iff (hgood : D.IsGoodCompletelySplitReduction)
    (A : D.GeometricPELDatum) :
    D.IsOrdinary (D.pointOfPEL hgood A) ↔
      Nat.card (A.data.polarized.abelian.torsionPoints q
        (Over.mk (𝟙 (Spec (.of (ModuliPoint.Construction.residueClosure q)))))) = q ^ (3 * s) := by
  have h := D.isOrdinary_iff_pointDatum_count (D.pointOfPEL hgood A)
  have hc := Nat.card_congr (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionPointsIso
    (D.pointOfPELDataIso hgood A).polarized.abelian q
      (Over.mk (𝟙 (Spec (.of (ModuliPoint.Construction.residueClosure q)))))).toEquiv
  exact h.trans (congrArg (fun n => n = q ^ (3 * s)) hc).to_iff

variable {D} {x : D.GeometricPoint} {m : ℕ}
variable {H : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ (D.pointDatum x).data.polarized.abelian.scheme}

theorem Integral.Construction.SplitPELReduction.QuotientWitness.targetPoint_ordinary
    (Q : D.QuotientWitness (D.pointDatum x) m H i)
    (hgood : D.IsGoodCompletelySplitReduction) (hx : D.IsOrdinary x) :
    D.IsOrdinary (D.pointOfPEL hgood Q.target) := by
  apply (D.isOrdinary_pointOfPEL_iff hgood Q.target).mpr
  have hc := PolarizedIsogenyOrdinary.Construction.polarizedIsogeny_torsionCard_preserved (D.pointDatum x).data.polarized.abelian
    Q.target.data.polarized.abelian (D.pointDatum x).data.polarized.dual
    (D.pointDatum x).data.polarized.polarization.isogeny Q.isogeny q (Fact.out : q.Prime).pos
  exact hc.symm.trans ((D.isOrdinary_iff_pointDatum_count x).mp hx)

def Integral.Construction.SplitPELReduction.QuotientWitness.ordinaryPoint
    (Q : D.QuotientWitness (D.pointDatum x) m H i)
    (hgood : D.IsGoodCompletelySplitReduction) (hx : D.IsOrdinary x) : D.OrdinaryPoint :=
  ⟨D.pointOfPEL hgood Q.target, Q.targetPoint_ordinary hgood hx⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
