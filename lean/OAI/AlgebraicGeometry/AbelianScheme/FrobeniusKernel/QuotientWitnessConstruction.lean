import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed

/-! # Quotient Witness Construction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The output required of a geometric PEL quotient. This is a result type,
not a source hypothesis: its existence requires construction of the full
target PEL object, including its Rosati and Lie conditions, and proofs of
the exact kernel, polarization multiplier, action and marking equations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

/-- An actual quotient with every component of the full PEL datum.
The opposite-annihilator prescription enters through the specified
embedded subgroup `i`; none of the operator identities is a field. -/
structure Integral.Construction.SplitPELReduction.QuotientWitness (source : D.GeometricPELDatum) (m : ℕ)
    (H : Grp (Over D.integralGeometricBase.left)) (i : H.X ⟶ source.data.polarized.abelian.scheme) where
  target : D.GeometricPELDatum
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny source.data.polarized.abelian target.data.polarized.abelian
  kernel : Prescribed.Construction.PrescribedKernel isogeny.hom i
  polarization : PolarizationComparison.Construction.polarizationPullbackHom isogeny.hom source.data.polarized.dual
    target.data.polarized.dual target.data.polarized.polarization =
      source.data.polarized.polarization.isogeny.hom ^ m
  action : ∀ a : NumberField.RingOfIntegers E,
    source.data.action.map a ≫ isogeny.hom = isogeny.hom ≫ target.data.action.map a
  marking : ∀ (T : (Over D.integralGeometricBase.left)ᵒᵖ)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor (3 * s) N D.integralGeometricBase.left).obj T),
    (target.data.polarized.level.hom.app T c).val =
      (source.data.polarized.level.hom.app T c).val ≫ isogeny.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
