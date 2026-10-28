import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.RationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport

/-! # Universal Level -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual reference-to-universal isomorphism preserves every
ordered original full-level label after the native fiber presentation. -/

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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso_level
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod D.pel.level)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (R.nativeUniversalFiberIso f x hx).hom
      ((R.family.marking.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase c)).val =
      Intrinsic.LevelTransport.presentedFullLevelPoint (Universal.PELConditions.complexUniversalPolarized D.pel hg f).level x
        (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x) c := by
  let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x
  have he := (R.universalFiberIso f x hx).marking (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase c)
  have hh := congrArg (fun u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints ((Complex.PELClassification.complexUniversalFamily D.pel f).pullback x.left).abelian.scheme =>
    u ≫ P.comparison.hom) he
  unfold Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso
  exact (Category.assoc _ _ _).symm.trans hh

end

end OAI.RepresentationTheory.Theta.Geometric
