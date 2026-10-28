import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestFiberIso
import OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
import OAI.RepresentationTheory.Theta.Geometric.ConjugatedIntertwining

/-! # Test Fiber Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The native comparison of an actual reference test fiber intertwines
every original integral endomorphism on the underlying schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.nativeReferenceTestFiberIso_action (b : NumberField.RingOfIntegers E) :
    let A := M.complexTestFamily κ f
    let Q := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y
    let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
    AbelianScheme.TateComparison.End.endSchemeMap R.abelian.toOver (R.functorAction b) ≫
        (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom =
      (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom ≫
        (Q.comparison.inv ≫ (A.action.pullback y.left).map b ≫ Q.comparison.hom) := by
  let A := M.complexTestFamily κ f
  let Q := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y
  let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
  let e := M.referenceTestFiberIso hM κ hP hκ f a y hy
  have he : AbelianScheme.TateComparison.End.endSchemeMap R.abelian.toOver (R.functorAction b) ≫ e.polarized.abelian.hom =
      e.polarized.abelian.hom ≫ (A.action.pullback y.left).map b := e.action b
  exact RepresentationTheory.Theta.Geometric.ConjugatedIntertwining.conjugated_intertwining e.polarized.abelian.hom Q.comparison
    (AbelianScheme.TateComparison.End.endSchemeMap R.abelian.toOver (R.functorAction b)) ((A.action.pullback y.left).map b) he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
