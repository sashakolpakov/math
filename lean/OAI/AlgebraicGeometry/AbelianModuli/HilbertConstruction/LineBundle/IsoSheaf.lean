import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.HomSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSheafGluing

/-! # Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSheaf

noncomputable section

/-! Actual isomorphisms between line bundles satisfy fppf and fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem lineBundleHom_isSheafFor_subcanonical (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (L M : Line.Bundles.LineBundle X) (T : Over X) (S : Sieve T) (hS : S ∈ (J.over X) T) :
    Presieve.IsSheafFor (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) S.arrows :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (HomSheaf.lineBundleHomPresheaf_isSheaf_subcanonical J L M) S hS

theorem lineBundleIsoPresheaf_isSheaf_subcanonical
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (J.over X) (Module.IsoPresheaf.moduleIsoPresheaf L.sheaf M.sheaf) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro T S hS
  exact Module.IsoSheafGluing.moduleIso_isSheafFor L.sheaf M.sheaf T S.arrows
    (lineBundleHom_isSheafFor_subcanonical J L M T S hS)
    (lineBundleHom_isSheafFor_subcanonical J M L T S hS)
    (lineBundleHom_isSheafFor_subcanonical J L L T S hS).isSeparatedFor
    (lineBundleHom_isSheafFor_subcanonical J M M T S hS).isSeparatedFor

theorem lineBundleIsoPresheaf_isSheaf_fppf (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (Module.IsoPresheaf.moduleIsoPresheaf L.sheaf M.sheaf) :=
  lineBundleIsoPresheaf_isSheaf_subcanonical Scheme.fppfTopology L M

theorem lineBundleIsoPresheaf_isSheaf_fpqc (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (Module.IsoPresheaf.moduleIsoPresheaf L.sheaf M.sheaf) :=
  lineBundleIsoPresheaf_isSheaf_subcanonical Scheme.fpqcTopology L M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSheaf
