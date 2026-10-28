import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

/-! # Quotient Witness Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotient witnesses with the same prescribed embedded kernel
and multiplier determine the same PEL moduli point. The complete
target-data isomorphism is the proved NeighborCounting construction at
b554cc2b3ba1e49848907ef9ceb533a94223b64a. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

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
variable (Q Q' : D.QuotientWitness source m H i)

def Integral.Construction.SplitPELReduction.QuotientWitness.targetDataIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso Q.target.data Q'.target.data :=
  Isogenies.NeighborCounting.Intrinsic.QuotientTargets.quotientWitnessIso Q Q'

theorem Integral.Construction.SplitPELReduction.QuotientWitness.targetDataIso_projection :
    Q.isogeny.hom ≫ (Q.targetDataIso Q').polarized.abelian.hom = Q'.isogeny.hom :=
  Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection Q.isogeny Q'.isogeny
    (fun T a => (Q.kernel T a).trans (Q'.kernel T a).symm)

theorem Integral.Construction.SplitPELReduction.QuotientWitness.point_eq (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood Q.target = D.pointOfPEL hgood Q'.target :=
  Isogenies.NeighborCounting.Intrinsic.QuotientTargets.quotientWitness_point_eq hgood Q Q'

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
