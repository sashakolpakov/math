import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Section Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport

noncomputable section

/-! Transporting a section and its fiber frame through the same bundle
isomorphism preserves its actual value. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X S : Scheme.{u}}

def transportedSectionFrame {L M : Line.Bundles.LineBundle X} (x : S ⟶ X) (h : L.sheaf ≅ M.sheaf)
    (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) :
    (M.pullback x).sheaf ≅ Line.Bundles.structureModule S :=
  (Scheme.Modules.pullback x).mapIso h.symm ≪≫ e

theorem familyFramedSectionValue_bundleIso {L M : Line.Bundles.LineBundle X}
    (x : S ⟶ X) (h : L.sheaf ≅ M.sheaf) (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S)
    (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Family.FramedSectionEvaluation.familyFramedSectionValue M x (transportedSectionFrame x h e) (a ≫ h.hom) =
      Family.FramedSectionEvaluation.familyFramedSectionValue L x e a := by
  unfold Family.FramedSectionEvaluation.familyFramedSectionValue
  rw [Power.SectionTransitions.pullbackSection_postcomp]
  congr 1
  change (Ample.LineBundles.pullbackSection x a ≫ ((Scheme.Modules.pullback x).mapIso h).hom) ≫
    (((Scheme.Modules.pullback x).mapIso h).inv ≫ e.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport
