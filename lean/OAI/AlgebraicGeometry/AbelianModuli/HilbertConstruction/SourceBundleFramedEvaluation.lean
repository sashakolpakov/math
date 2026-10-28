import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoSchemeSectionEquiv
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition

/-! # Source Bundle Framed Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourceBundleFramedEvaluation

noncomputable section

/-! Transporting both a section and its fiber frame through a source
map and a line-bundle isomorphism preserves its exact framed value.
For a source isomorphism this identifies the actual linear evaluation maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y S : Scheme.{u}}

def compositeSectionFrame (L : Line.Bundles.LineBundle Y) (x : S ⟶ X) (f : X ⟶ Y)
    (e : (L.pullback (x ≫ f)).sheaf ≅ Line.Bundles.structureModule S) :
    ((L.pullback f).pullback x).sheaf ≅ Line.Bundles.structureModule S :=
  (Scheme.Modules.pullbackComp x f).app L.sheaf ≪≫ e

def sourceBundleSectionFrame (L : Line.Bundles.LineBundle Y) (M : Line.Bundles.LineBundle X) (x : S ⟶ X) (f : X ⟶ Y)
    (H : (L.pullback f).sheaf ≅ M.sheaf)
    (e : (L.pullback (x ≫ f)).sheaf ≅ Line.Bundles.structureModule S) :
    (M.pullback x).sheaf ≅ Line.Bundles.structureModule S :=
  Framed.SectionBundleTransport.transportedSectionFrame x H (compositeSectionFrame L x f e)

theorem familyFramedSectionValue_composite (L : Line.Bundles.LineBundle Y) (x : S ⟶ X) (f : X ⟶ Y)
    (e : (L.pullback (x ≫ f)).sheaf ≅ Line.Bundles.structureModule S) (a : Line.Bundles.structureModule Y ⟶ L.sheaf) :
    Family.FramedSectionEvaluation.familyFramedSectionValue (L.pullback f) x (compositeSectionFrame L x f e) (Ample.LineBundles.pullbackSection f a) =
      Family.FramedSectionEvaluation.familyFramedSectionValue L (x ≫ f) e a := by
  unfold Family.FramedSectionEvaluation.familyFramedSectionValue compositeSectionFrame
  rw [Iso.trans_hom, ← Category.assoc]
  erw [Global.SectionPullbackComposition.pullbackSection_composition]

theorem familyFramedSectionValue_sourceBundle (L : Line.Bundles.LineBundle Y) (M : Line.Bundles.LineBundle X)
    (x : S ⟶ X) (f : X ⟶ Y) (H : (L.pullback f).sheaf ≅ M.sheaf)
    (e : (L.pullback (x ≫ f)).sheaf ≅ Line.Bundles.structureModule S) (a : Line.Bundles.structureModule Y ⟶ L.sheaf) :
    Family.FramedSectionEvaluation.familyFramedSectionValue M x (sourceBundleSectionFrame L M x f H e)
      (Ample.LineBundles.pullbackSection f a ≫ H.hom) = Family.FramedSectionEvaluation.familyFramedSectionValue L (x ≫ f) e a :=
  (Framed.SectionBundleTransport.familyFramedSectionValue_bundleIso x H (compositeSectionFrame L x f e) (Ample.LineBundles.pullbackSection f a)).trans
    (familyFramedSectionValue_composite L x f e a)

theorem affineFramedSectionValue_sourceBundle {R : Type u} [CommRing R]
    (L : Line.Bundles.LineBundle Y) (M : Line.Bundles.LineBundle X) (x : Spec (.of R) ⟶ X) (f : X ⟶ Y)
    (H : (L.pullback f).sheaf ≅ M.sheaf)
    (e : (L.pullback (x ≫ f)).sheaf ≅ Line.Bundles.structureModule (Spec (.of R)))
    (a : Line.Bundles.structureModule Y ⟶ L.sheaf) :
    Affine.FramedSectionEvaluation.affineFramedSectionValue M x (sourceBundleSectionFrame L M x f H e)
      (Ample.LineBundles.pullbackSection f a ≫ H.hom) = Affine.FramedSectionEvaluation.affineFramedSectionValue L (x ≫ f) e a :=
  congrArg (Scheme.ΓSpecIso (.of R)).hom (familyFramedSectionValue_sourceBundle L M x f H e a)

theorem affineFramedSectionEvaluation_sourceBundleIso
    {R : Type u} [CommRing R] {A B : Over (Spec (.of R))} (f : A ≅ B)
    (L : Line.Bundles.LineBundle B.left) (M : Line.Bundles.LineBundle A.left)
    (x : Spec (.of R) ⟶ A.left) (hx : x ≫ A.hom = 𝟙 _)
    (H : (L.pullback f.hom.left).sheaf ≅ M.sheaf)
    (e : (L.pullback (x ≫ f.hom.left)).sheaf ≅ Line.Bundles.structureModule (Spec (.of R)))
    (hz : (x ≫ f.hom.left) ≫ B.hom = 𝟙 _) :
    (Affine.FramedSectionEvaluation.affineFramedSectionEvaluation A.hom M x hx (sourceBundleSectionFrame L M x f.hom.left H e)).comp
      (IsoSchemeSectionEquiv.sourceBundleIsoSchemeSectionEquiv f L.sheaf H).toLinearMap =
      Affine.FramedSectionEvaluation.affineFramedSectionEvaluation B.hom L (x ≫ f.hom.left) hz e := by
  apply LinearMap.ext
  intro v
  obtain ⟨a, rfl⟩ := (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap B.hom) L.sheaf).surjective v
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, IsoSchemeSectionEquiv.sourceBundleIsoSchemeSectionEquiv_section,
    Affine.FramedSectionEvaluation.affineFramedSectionEvaluation_section, Affine.FramedSectionEvaluation.affineFramedSectionEvaluation_section]
  exact affineFramedSectionValue_sourceBundle L M x f.hom.left H e a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourceBundleFramedEvaluation
