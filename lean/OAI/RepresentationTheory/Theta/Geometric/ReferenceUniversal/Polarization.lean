import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.RationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Reference.ToPolarizedForm

/-! # Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The reference marking of the actual universal fiber carries the
original trace polarization with its exact normalization. -/

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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso_hom :
    (R.nativeUniversalFiberIso f x hx).hom = (R.universalFiberIso f x hx).abelian.hom := by
  unfold Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso
  apply Over.OverMorphism.ext
  change (R.universalFiberIso f x hx).abelian.hom.left ≫ 𝟙 _ = _
  exact Category.comp_id _

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking PolarizedCanonicalForm.familyPolarizationForm
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    PolarizedCanonicalForm.familyPolarizationForm (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x
      (R.nativeUniversalRationalMarking f x hx v) (R.nativeUniversalRationalMarking f x hx w) =
        D.pel.reference.traceForm v w := by
  let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
  let B := A.pullback x.left
  let M := R.model.toNativeReferenceModel R.analytic
  let e := R.universalFiberIso f x hx
  let : IsMonHom e.abelian.hom := e.abelianGroup
  let : IsMonHom e.dual.hom := e.dualGroup
  let en := R.nativeUniversalFiberIso f x hx
  let : IsMonHom en.hom := R.nativeUniversalFiberIso_group f x hx
  have hh := R.nativeUniversalFiberIso_hom f x hx
  have hform := Reference.ToPolarizedForm.referenceToPolarized_period_form R.polarization B e.abelian e.dual
    e.polarization e.poincare (M.nativeReferenceMarking v) (M.nativeReferenceMarking w)
  unfold Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking PolarizedCanonicalForm.familyPolarizationForm
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom (M.nativeReferenceMarking v))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom (M.nativeReferenceMarking w)) = _
  have hv := LinearMap.congr_fun (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ hh) (M.nativeReferenceMarking v)
  have hw := LinearMap.congr_fun (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ hh) (M.nativeReferenceMarking w)
  exact (congrArg₂ (fun u t => AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B u t) hv hw).trans
    (hform.trans (R.polarization.chern v w))

end

end OAI.RepresentationTheory.Theta.Geometric
