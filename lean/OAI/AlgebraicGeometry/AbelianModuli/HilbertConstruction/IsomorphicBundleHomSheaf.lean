import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleMapScalarNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionSheaf

/-! # Isomorphic Bundle Hom Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicBundleHomSheaf

noncomputable section

/-! Maps between two isomorphic line bundles satisfy fppf and fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def lineBundleHomPresheafScalarIso (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf ≅ Relative.AffineLineFunctions.relativeFunctionPresheaf X :=
  NatIso.ofComponents (fun T => (BundleMapScalarNaturality.lineBundleHomScalarEquiv L M e T.unop).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro φ
    exact BundleMapScalarNaturality.lineBundleHomScalarEquiv_naturality L M e f.unop φ)

theorem lineBundleHomPresheaf_isSheaf_fppf_of_iso (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) :=
  (Presheaf.isSheaf_of_iso_iff (lineBundleHomPresheafScalarIso L M e)).mpr
    (Relative.FunctionSheaf.relativeFunctionPresheaf_isSheaf_fppf X)

theorem lineBundleHomPresheaf_isSheaf_fpqc_of_iso (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) :=
  (Presheaf.isSheaf_of_iso_iff (lineBundleHomPresheafScalarIso L M e)).mpr
    (Relative.FunctionSheaf.relativeFunctionPresheaf_isSheaf_fpqc X)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicBundleHomSheaf
