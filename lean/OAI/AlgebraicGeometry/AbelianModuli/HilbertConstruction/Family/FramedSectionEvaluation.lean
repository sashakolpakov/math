import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

/-! # Framed Section Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation

noncomputable section

/-! A section of a family and a frame of its pulled-back line bundle
give a linear evaluation map over the actual global ring of the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} (p : X ⟶ S) (L : Line.Bundles.LineBundle X)
variable (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
variable (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S)

def familyFramedSectionValue (a : Line.Bundles.structureModule X ⟶ L.sheaf) : Γ(S, ⊤) :=
  Frame.Coordinates.structureModuleEndValue S (Ample.LineBundles.pullbackSection x a ≫ e.hom)

theorem familyFramedSectionValue_add (a b : Line.Bundles.structureModule X ⟶ L.sheaf) :
    familyFramedSectionValue L x e (a + b) =
      familyFramedSectionValue L x e a + familyFramedSectionValue L x e b := by
  unfold familyFramedSectionValue
  erw [Section.NonvanishingAddition.pullbackSection_add, Preadditive.add_comp, map_add]

include hx in
theorem familyFramedSectionValue_scalar (r : Γ(S, ⊤)) (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    familyFramedSectionValue L x e (Scalar.SectionValues.scalarSection (p.appTop r) a) =
      r * familyFramedSectionValue L x e a := by
  have hc : x.appTop (p.appTop r) = r := by
    change (x ≫ p).appTop r = r
    rw [hx]
    rfl
  unfold familyFramedSectionValue
  rw [Coefficient.RingSectionBasis.pullbackSection_scalarSection, hc]
  rw [show Scalar.SectionValues.scalarSection r (Ample.LineBundles.pullbackSection x a) ≫ e.hom =
    Scalar.SectionValues.scalarSection r (Ample.LineBundles.pullbackSection x a ≫ e.hom) from Category.assoc _ _ _]
  exact Scalar.SectionValues.scalarSection_globalValue r (Ample.LineBundles.pullbackSection x a ≫ e.hom)

def familyFramedSectionEvaluation :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj L.sheaf →ₗ[Γ(S, ⊤)] Γ(S, ⊤) where
  toFun v := familyFramedSectionValue L x e
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf).symm v)
  map_add' v w := by
    erw [map_add]
    exact familyFramedSectionValue_add L x e _ _
  map_smul' r v := by
    have he : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf).symm (r • v) =
        Scalar.SectionValues.scalarSection (p.appTop r) ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf).injective
      erw [AddEquiv.apply_symm_apply, Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar,
        AddEquiv.apply_symm_apply]
    rw [he]
    exact familyFramedSectionValue_scalar p L x hx e r _

theorem familyFramedSectionEvaluation_section (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    familyFramedSectionEvaluation p L x hx e (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf a) =
      familyFramedSectionValue L x e a := by
  change familyFramedSectionValue L x e
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf).symm
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv p.appTop.hom L.sheaf a)) = _
  rw [AddEquiv.symm_apply_apply]

theorem familyFramedSectionValue_nonvanishing (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    S.basicOpen (familyFramedSectionValue L x e a) = x ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing a := by
  unfold familyFramedSectionValue
  rw [← Scalar.Nonvanishing.sectionNonvanishing_scalar, Ample.Powers.sectionNonvanishing_comp_iso, LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange x L a]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
