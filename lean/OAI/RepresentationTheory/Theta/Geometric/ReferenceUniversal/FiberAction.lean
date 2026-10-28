import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.FiberIso
import OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
import OAI.RepresentationTheory.Theta.Geometric.ConjugatedIntertwining
import OAI.RepresentationTheory.Theta.Geometric.PELActionPullback

/-! # Fiber Action -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The reference-to-universal native comparison intertwines the
original integral PEL endomorphisms on the actual schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso_action (b : NumberField.RingOfIntegers E) :
    let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action b) ≫ (R.nativeUniversalFiberIso f x hx).hom =
      (R.nativeUniversalFiberIso f x hx).hom ≫
        (P.comparison.inv ≫ ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback x.left).map b ≫ P.comparison.hom) := by
  let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x
  let e := R.universalFiberIso f x hx
  have hb : AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap ((Complex.PELClassification.complexUniversalFamily D.pel f).pullback x.left).abelian.scheme
      (((Complex.PELClassification.complexUniversalFamily D.pel f).pullback x.left).action b) =
      ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback x.left).map b :=
    PELActionPullback.pelAction_pullback_schemeMap (Complex.PELClassification.complexUniversalFamily D.pel f) x.left b
  have he : AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action b) ≫ e.abelian.hom =
      e.abelian.hom ≫ ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback x.left).map b :=
    (e.equivariant b).trans (congrArg (fun k => e.abelian.hom ≫ k) hb)
  exact ConjugatedIntertwining.conjugated_intertwining e.abelian.hom P.comparison
    (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action b))
    (((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback x.left).map b) he

end

end OAI.RepresentationTheory.Theta.Geometric
