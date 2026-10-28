import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.FiberAction
import OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
import OAI.RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining

/-! # Rational Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A reference moduli point supplies an actual rational marking of
the universal fiber, commuting with every original integral action. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

def Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ]
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).variety := by
  let : IsMonHom (R.nativeUniversalFiberIso f x hx).hom := R.nativeUniversalFiberIso_group f x hx
  exact (R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking.trans
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (R.nativeUniversalFiberIso f x hx))

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking_integer (b : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.nativeUniversalRationalMarking f x hx ((b : E) • v) =
      Family.FieldActions.familyIntegralPeriodAction (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x b
        (R.nativeUniversalRationalMarking f x hx v) := by
  let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x
  let e := R.nativeUniversalFiberIso f x hx
  let M := R.model.toNativeReferenceModel R.analytic
  let : IsMonHom e.hom := R.nativeUniversalFiberIso_group f x hx
  let : IsMonHom P.comparison.hom := P.comparison_group
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (M.nativeReferenceMarking ((b : E) • v)) =
    Family.FieldActions.familyIntegralPeriodAction (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x b
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (M.nativeReferenceMarking v))
  rw [Family.FieldActions.familyIntegralPeriodAction_presented, ← M.nativeReferenceMarking_action]
  exact Rational.LiftIntertwining.rationalLift_intertwining_apply e.hom
    (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action b))
    (P.comparison.inv ≫ ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback x.left).map b ≫ P.comparison.hom)
    (R.nativeUniversalFiberIso_action f x hx b) (M.nativeReferenceMarking v)

end

end OAI.RepresentationTheory.Theta.Geometric
