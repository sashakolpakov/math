import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestFiberAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction
import OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
import OAI.RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining

/-! # Test Rational Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual reference-to-test isomorphism supplies a native rational
period marking that commutes with every original integral CM action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

def Models.FinePELModel.nativeReferenceTestRationalMarking : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ]
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety := by
  let : GrpObj (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver :=
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.group
  have : IsMonHom (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom :=
    M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy
  exact (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP).nativeReferenceMarking.trans
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy))

theorem Models.FinePELModel.nativeReferenceTestRationalMarking_integer
    (b : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy ((b : E) • v) =
      RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y b
        (M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy v) := by
  let A := M.complexTestFamily κ f
  let Q := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y
  let e := M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy
  let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
  let : GrpObj Q.variety.toOver := Q.variety.group
  have : IsMonHom e.hom := M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy
  have : IsMonHom Q.comparison.hom := Q.comparison_group
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (R.nativeReferenceMarking ((b : E) • v)) =
    RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction A.polarized A.action y b (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (R.nativeReferenceMarking v))
  rw [RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction_presented, ← R.nativeReferenceMarking_action]
  exact RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining.rationalLift_intertwining_apply e.hom
    (AbelianScheme.TateComparison.End.endSchemeMap R.abelian.toOver (R.functorAction b))
    (Q.comparison.inv ≫ (A.action.pullback y.left).map b ≫ Q.comparison.hom)
    (M.nativeReferenceTestFiberIso_action hM κ hP hκ f a y hy b) (R.nativeReferenceMarking v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
