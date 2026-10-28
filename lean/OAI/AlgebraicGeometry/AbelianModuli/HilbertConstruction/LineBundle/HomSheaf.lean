import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomZariskiSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomLocalSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSieve
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionsSubcanonicalSheaf

/-! # Hom Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.HomSheaf

noncomputable section

/-! Maps between arbitrary line bundles satisfy fppf and fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem lineBundleHomPresheaf_isSheaf_subcanonical
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (J.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro T S hS
  apply Presieve.isSheafFor_trans (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) (IsoSieve.lineBundleIsoSieve L M T) S
  · exact Module.HomZariskiSheaf.moduleHom_isSheafFor_zariski L.sheaf M.sheaf T _ (IsoSieve.lineBundleIsoSieve_mem_zariski L M T)
  · intro Y f _
    exact Module.HomZariskiSheaf.moduleHom_isSeparatedFor_zariski L.sheaf M.sheaf Y _
      ((Scheme.zariskiTopology.over X).pullback_stable f (IsoSieve.lineBundleIsoSieve_mem_zariski L M T))
  · intro Y f hf
    obtain ⟨e⟩ := hf
    exact Module.HomLocalSheaf.moduleHom_isSheafFor_of_baseChange Y J L.sheaf M.sheaf
      (Relative.FunctionsSubcanonicalSheaf.lineBundleHomPresheaf_isSheaf_subcanonical_of_iso J (L.pullback Y.hom) (M.pullback Y.hom) e)
      (S.pullback f) ((J.over X).pullback_stable f hS)

theorem lineBundleHomPresheaf_isSheaf_fppf (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) :=
  lineBundleHomPresheaf_isSheaf_subcanonical Scheme.fppfTopology L M

theorem lineBundleHomPresheaf_isSheaf_fpqc (L M : Line.Bundles.LineBundle X) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) :=
  lineBundleHomPresheaf_isSheaf_subcanonical Scheme.fpqcTopology L M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.HomSheaf
