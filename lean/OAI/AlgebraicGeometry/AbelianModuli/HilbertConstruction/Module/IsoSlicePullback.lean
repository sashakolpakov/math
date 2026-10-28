import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition

/-! # Iso Slice Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback

noncomputable section

/-! Functorial pullback of actual module isomorphisms over a base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleMapPullbackAlong_map_id {U V : Over X} (a : U ⟶ V) (M : X.Modules) :
    MapSlicePullback.moduleMapPullbackAlong a (𝟙 ((Scheme.Modules.pullback V.hom).obj M)) =
      𝟙 ((Scheme.Modules.pullback U.hom).obj M) := by
  have h := HomPresheaf.moduleMapPullbackAlong_of_map a (𝟙 M)
  rw [(Scheme.Modules.pullback V.hom).map_id, (Scheme.Modules.pullback U.hom).map_id] at h
  exact h

def moduleIsoPullbackAlong {U V : Over X} (a : U ⟶ V) {M N : X.Modules}
    (e : (Scheme.Modules.pullback V.hom).obj M ≅ (Scheme.Modules.pullback V.hom).obj N) :
    (Scheme.Modules.pullback U.hom).obj M ≅ (Scheme.Modules.pullback U.hom).obj N where
  hom := MapSlicePullback.moduleMapPullbackAlong a e.hom
  inv := MapSlicePullback.moduleMapPullbackAlong a e.inv
  hom_inv_id := by
    rw [← MapSliceComposition.moduleMapPullbackAlong_map_comp, e.hom_inv_id, moduleMapPullbackAlong_map_id]
  inv_hom_id := by
    rw [← MapSliceComposition.moduleMapPullbackAlong_map_comp, e.inv_hom_id, moduleMapPullbackAlong_map_id]

theorem moduleIsoPullbackAlong_id (U : Over X) {M N : X.Modules}
    (e : (Scheme.Modules.pullback U.hom).obj M ≅ (Scheme.Modules.pullback U.hom).obj N) :
    moduleIsoPullbackAlong (𝟙 U) e = e := by
  apply Iso.ext
  exact MapSlicePullback.moduleMapPullbackAlong_id U e.hom

theorem moduleIsoPullbackAlong_comp {U V W : Over X} (a : U ⟶ V) (b : V ⟶ W) {M N : X.Modules}
    (e : (Scheme.Modules.pullback W.hom).obj M ≅ (Scheme.Modules.pullback W.hom).obj N) :
    moduleIsoPullbackAlong a (moduleIsoPullbackAlong b e) = moduleIsoPullbackAlong (a ≫ b) e := by
  apply Iso.ext
  exact MapSlicePullback.moduleMapPullbackAlong_comp a b e.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback
