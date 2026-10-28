import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.RationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Family.PELCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity

/-! # Field Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original integral-action comparison extends the reference
marking to a linear equivalence over the entire CM field. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

def Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFieldMarking :
    let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
    let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety := by
  let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
  let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  let q := R.nativeUniversalRationalMarking f x hx
  let m := Rational.CMLinearity.rationalMapToCMLinear (E := E) q.toLinearMap (fun b v => by
    change q ((b : E) • v) = Family.FieldActions.familyFieldPeriodAction A ρ x (b : E) (q v)
    rw [Family.FieldActions.familyFieldPeriodAction_integer]
    exact R.nativeUniversalRationalMarking_integer f x hx b v)
  exact LinearEquiv.ofBijective m q.bijective

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFieldMarking_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.nativeUniversalFieldMarking f x hx v = R.nativeUniversalRationalMarking f x hx v := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
