import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicBundleHomSheaf

/-! # Functions Subcanonical Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionsSubcanonicalSheaf

noncomputable section

/-! Regular functions and maps between isomorphic line bundles are sheaves for subcanonical topologies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]

theorem relativeFunctionPresheaf_isSheaf_subcanonical (S : Scheme.{u}) :
    Presheaf.IsSheaf (J.over S) (AffineLineFunctions.relativeFunctionPresheaf S) :=
  (Presheaf.isSheaf_of_iso_iff (J := J.over S) (AffineLineFunctions.relativeFunctionPresheafIso S)).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

theorem lineBundleHomPresheaf_isSheaf_subcanonical_of_iso {X : Scheme.{u}}
    (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    Presheaf.IsSheaf (J.over X) (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf) :=
  (Presheaf.isSheaf_of_iso_iff (IsomorphicBundleHomSheaf.lineBundleHomPresheafScalarIso L M e)).mpr
    (relativeFunctionPresheaf_isSheaf_subcanonical J X)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionsSubcanonicalSheaf
