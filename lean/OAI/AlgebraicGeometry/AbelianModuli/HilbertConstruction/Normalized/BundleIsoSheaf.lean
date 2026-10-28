import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleIsoSectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafFiberSheaf

/-! # Bundle Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoSheaf

noncomputable section

/-! Bundle isomorphisms with a prescribed restriction to a section satisfy descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
variable (L M : Line.Bundles.LineBundle X)
variable (b : (Scheme.Modules.pullback x).obj L.sheaf ≅ (Scheme.Modules.pullback x).obj M.sheaf)

def normalizedBundleIsoPresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  (PresheafFiberSheaf.presheafSectionFiber (BundleIsoSectionRestriction.bundleIsoRestrictionToSection p x hx L M)
    (Module.IsoBaseChange.globalModuleIsoSection _ _ b)).toFunctor

theorem normalizedBundleIsoPresheaf_isSheaf_subcanonical
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf (J.over S) (normalizedBundleIsoPresheaf p x hx L M b) :=
  PresheafFiberSheaf.presheafSectionFiber_isSheaf (J.over S) _ _
    (Relative.BundleIsoSheaf.relativeBundleIsoPresheaf_isSheaf_subcanonical p L M J)
    (LineBundle.IsoSheaf.lineBundleIsoPresheaf_isSheaf_subcanonical J (L.pullback x) (M.pullback x))

theorem normalizedBundleIsoPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (normalizedBundleIsoPresheaf p x hx L M b) :=
  normalizedBundleIsoPresheaf_isSheaf_subcanonical p x hx L M b Scheme.fppfTopology

theorem normalizedBundleIsoPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (normalizedBundleIsoPresheaf p x hx L M b) :=
  normalizedBundleIsoPresheaf_isSheaf_subcanonical p x hx L M b Scheme.fpqcTopology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoSheaf
