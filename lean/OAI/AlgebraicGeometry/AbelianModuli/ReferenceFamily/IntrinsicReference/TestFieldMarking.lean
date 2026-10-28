import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestRationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Family.PELCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity

/-! # Test Field Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The integral-action comparison extends the constructed native
reference marking to a linear equivalence over the entire CM field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestRationalMarking

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

def Models.FinePELModel.nativeReferenceTestFieldMarking :
    let A := M.complexTestFamily κ f
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action y
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y).variety := by
  let A := M.complexTestFamily κ f
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A.polarized A.action y
  let q := M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy
  let m := RepresentationTheory.Theta.Geometric.Rational.CMLinearity.rationalMapToCMLinear (E := E) q.toLinearMap (fun b v => by
    change q ((b : E) • v) = RepresentationTheory.Theta.Geometric.Family.FieldActions.familyFieldPeriodAction A.polarized A.action y (b : E) (q v)
    rw [RepresentationTheory.Theta.Geometric.Family.FieldActions.familyFieldPeriodAction_integer]
    exact M.nativeReferenceTestRationalMarking_integer hM κ hP hκ f a y hy b v)
  exact LinearEquiv.ofBijective m q.bijective

theorem Models.FinePELModel.nativeReferenceTestFieldMarking_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy v =
      M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy v := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
