import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

/-! # Bundle Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleNormalization.Construction

noncomputable section

/-! Line-bundle isomorphisms on a proper smooth pointed family over
a locally Noetherian base have unique prescribed normalization at the section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S X : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)

include hσ in
theorem noetherian_section_globalFunctions_isIso : IsIso σ.appTop := by
  have : IsIso f.appTop := GlobalFunctions.Construction.noetherian_globalFunctions_isIso f σ hσ
  exact AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants.section_globalFunctions_isIso f σ hσ

include hσ in
theorem noetherian_bundleIso_ext (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback σ).map a.hom = (Scheme.Modules.pullback σ).map b.hom) : a = b := by
  have : IsIso σ.appTop := noetherian_section_globalFunctions_isIso f σ hσ
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.iso_eq_of_globalFunctions _ (ConcreteCategory.bijective_of_isIso _).1 L M a b h

include hσ in
theorem noetherian_existsUnique_bundleIso_with_section_fiber
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hLM : Nonempty (L.sheaf ≅ M.sheaf))
    (b : (L.pullback σ).sheaf ≅ (M.pullback σ).sheaf) :
    ∃! a : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback σ).map a.hom = b.hom := by
  have : IsIso σ.appTop := noetherian_section_globalFunctions_isIso f σ hσ
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.existsUnique_iso_with_pullback _ (ConcreteCategory.bijective_of_isIso _) L M hLM b

include hσ in
theorem noetherian_rigidifiedBundleIso_subsingleton (L M : AbelianModuli.HilbertConstruction.RigidifiedLineBundles.RigidifiedLineBundle σ) :
    Subsingleton (AbelianModuli.HilbertConstruction.RigidifiedLineBundles.RigidifiedLineBundleIso L M) := by
  have : IsIso σ.appTop := noetherian_section_globalFunctions_isIso f σ hσ
  exact AbelianModuli.HilbertConstruction.RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions _ (ConcreteCategory.bijective_of_isIso _).1 L M

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleNormalization.Construction
