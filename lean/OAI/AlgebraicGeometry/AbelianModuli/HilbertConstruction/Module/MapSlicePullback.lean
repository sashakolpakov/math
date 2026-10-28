import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion

/-! # Map Slice Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback

noncomputable section

/-! Functorial pullback of module maps on schemes over a fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleMapPullbackComp_assoc_forward {W Y Z : Scheme.{u}}
    (a : W ⟶ Y) (b : Y ⟶ Z) (f : Z ⟶ X) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    MapPullbackComposition.moduleMapPullbackComp a (b ≫ f) (MapPullbackComposition.moduleMapPullbackComp b f φ) =
      MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f) (MapPullbackComposition.moduleMapPullbackComp (a ≫ b) f φ) := by
  have h : MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f).symm
      (MapPullbackComposition.moduleMapPullbackComp a (b ≫ f) (MapPullbackComposition.moduleMapPullbackComp b f φ)) =
        MapPullbackComposition.moduleMapPullbackComp (a ≫ b) f φ := MapPullbackComposition.moduleMapPullbackComp_assoc a b f φ
  have h' := congrArg (fun k => MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f) k) h
  rw [MapPullbackCongruence.moduleMapPullbackCongr_trans] at h'
  simpa only [MapPullbackCongruence.moduleMapPullbackCongr_refl] using h'

def moduleMapPullbackAlong {U V : Over X} (a : U ⟶ V) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) :
    (Scheme.Modules.pullback U.hom).obj M ⟶ (Scheme.Modules.pullback U.hom).obj N :=
  MapPullbackCongruence.moduleMapPullbackCongr a.w (MapPullbackComposition.moduleMapPullbackComp a.left V.hom φ)

theorem moduleMapPullbackAlong_comp {U V W : Over X} (a : U ⟶ V) (b : V ⟶ W)
    {M N : X.Modules}
    (φ : (Scheme.Modules.pullback W.hom).obj M ⟶ (Scheme.Modules.pullback W.hom).obj N) :
    moduleMapPullbackAlong a (moduleMapPullbackAlong b φ) = moduleMapPullbackAlong (a ≫ b) φ := by
  unfold moduleMapPullbackAlong
  rw [← MapPullbackCongruence.moduleMapPullbackComp_congr_base a.left b.w, MapPullbackCongruence.moduleMapPullbackCongr_trans,
    moduleMapPullbackComp_assoc_forward, MapPullbackCongruence.moduleMapPullbackCongr_trans]
  rfl

theorem moduleMapPullbackAlong_id (U : Over X) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback U.hom).obj M ⟶ (Scheme.Modules.pullback U.hom).obj N) :
    moduleMapPullbackAlong (𝟙 U) φ = φ := by
  unfold moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  rw [MapPullbackComposition.moduleMap_homCongr_combine]
  change Iso.homCongr
      ((Scheme.Modules.pullbackComp (𝟙 U.left) U.hom).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp U.hom)).app M)
      ((Scheme.Modules.pullbackComp (𝟙 U.left) U.hom).app N ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp U.hom)).app N)
      ((Scheme.Modules.pullback (𝟙 U.left)).map φ) = φ
  rw [Pullback.UnitFusion.modulePullback_identity_fusion, Pullback.UnitFusion.modulePullback_identity_fusion]
  exact MapPullbackComposition.moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackId U.left) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback
