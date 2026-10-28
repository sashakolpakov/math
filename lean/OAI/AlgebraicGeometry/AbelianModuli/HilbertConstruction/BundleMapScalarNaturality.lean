import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndDescent

/-! # Bundle Map Scalar Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Scalars of endomorphisms and coordinates of maps between isomorphic bundles
are compatible with the presheaf pullback maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.endScalar_pullbackAlong (L : Line.Bundles.LineBundle X) {U V : Over X}
    (a : U ⟶ V) (φ : End (L.pullback V.hom).sheaf) :
    (L.pullback U.hom).endScalar (Module.MapSlicePullback.moduleMapPullbackAlong a φ) =
      a.left.appTop ((L.pullback V.hom).endScalar φ) :=
  (Line.Bundles.LineBundle.endScalar_transport (L.pullback (a.left ≫ V.hom)) (L.pullback U.hom)
    ((Scheme.Modules.pullbackCongr a.w).app L.sheaf) (Module.MapPullbackComposition.moduleMapPullbackComp a.left V.hom φ)).trans
      (L.endScalar_pullbackMapComp a.left V.hom φ)

def BundleMapScalarNaturality.lineBundleHomScalarEquiv (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) (T : Over X) :
    (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf).obj (.op T) ≃ Γ(T.left, ⊤) :=
  (Iso.homCongr (Iso.refl _) ((Scheme.Modules.pullback T.hom).mapIso e).symm).trans
    (L.pullback T.hom).endScalarRingEquiv.toEquiv

theorem BundleMapScalarNaturality.lineBundleHomScalarEquiv_apply (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (T : Over X) (φ : (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf).obj (.op T)) :
    BundleMapScalarNaturality.lineBundleHomScalarEquiv L M e T φ =
      (L.pullback T.hom).endScalar (φ ≫ (Scheme.Modules.pullback T.hom).map e.inv) := by
  change (L.pullback T.hom).endScalar (𝟙 _ ≫ φ ≫ (Scheme.Modules.pullback T.hom).map e.inv) = _
  rw [Category.id_comp]

theorem BundleMapScalarNaturality.lineBundleHomScalarEquiv_naturality (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf)
    {U V : Over X} (a : U ⟶ V) (φ : (Module.HomPresheaf.moduleHomPresheaf L.sheaf M.sheaf).obj (.op V)) :
    BundleMapScalarNaturality.lineBundleHomScalarEquiv L M e U (Module.MapSlicePullback.moduleMapPullbackAlong a φ) =
      a.left.appTop (BundleMapScalarNaturality.lineBundleHomScalarEquiv L M e V φ) := by
  change (Scheme.Modules.pullback V.hom).obj L.sheaf ⟶
    (Scheme.Modules.pullback V.hom).obj M.sheaf at φ
  have h : Module.MapSlicePullback.moduleMapPullbackAlong a (φ ≫ (Scheme.Modules.pullback V.hom).map e.inv) =
      Module.MapSlicePullback.moduleMapPullbackAlong a φ ≫ (Scheme.Modules.pullback U.hom).map e.inv := by
    rw [Module.MapSliceComposition.moduleMapPullbackAlong_map_comp, Module.HomPresheaf.moduleMapPullbackAlong_of_map]
  exact (BundleMapScalarNaturality.lineBundleHomScalarEquiv_apply L M e U (Module.MapSlicePullback.moduleMapPullbackAlong a φ)).trans
    (((congrArg (L.pullback U.hom).endScalar h).symm.trans
      (L.endScalar_pullbackAlong a (φ ≫ (Scheme.Modules.pullback V.hom).map e.inv))).trans
        (congrArg (fun r => a.left.appTop r) (BundleMapScalarNaturality.lineBundleHomScalarEquiv_apply L M e V φ).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
