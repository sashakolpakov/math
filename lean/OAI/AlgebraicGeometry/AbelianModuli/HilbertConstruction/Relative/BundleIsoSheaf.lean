import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSheaf

/-! # Bundle Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf

noncomputable section

/-! Bundle isomorphisms on the base changes of a fixed family form a sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (L M : Line.Bundles.LineBundle X)

def relativeBundleIsoPresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.pullback p).op ⋙ Module.IsoPresheaf.moduleIsoPresheaf L.sheaf M.sheaf

theorem relativeBundleIsoPresheaf_isSheaf_subcanonical
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf (J.over S) (relativeBundleIsoPresheaf p L M) :=
  (Over.pullback p).op_comp_isSheaf_of_isSheaf (J.over S) (J.over X) _
    (LineBundle.IsoSheaf.lineBundleIsoPresheaf_isSheaf_subcanonical J L M)

theorem relativeBundleIsoPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (relativeBundleIsoPresheaf p L M) :=
  relativeBundleIsoPresheaf_isSheaf_subcanonical p L M Scheme.fppfTopology

theorem relativeBundleIsoPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (relativeBundleIsoPresheaf p L M) :=
  relativeBundleIsoPresheaf_isSheaf_subcanonical p L M Scheme.fpqcTopology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf
