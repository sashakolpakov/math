import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf

/-! # Map Slice Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition

noncomputable section

/-! Pullback on the presheaf of module maps preserves composition and isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {U V : Over X}

theorem moduleMapPullbackAlong_map_comp (a : U ⟶ V) {M N P : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N)
    (ψ : (Scheme.Modules.pullback V.hom).obj N ⟶ (Scheme.Modules.pullback V.hom).obj P) :
    MapSlicePullback.moduleMapPullbackAlong a (φ ≫ ψ) = MapSlicePullback.moduleMapPullbackAlong a φ ≫ MapSlicePullback.moduleMapPullbackAlong a ψ := by
  unfold MapSlicePullback.moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  rw [Functor.map_comp, Iso.homCongr_comp, Iso.homCongr_comp]

theorem moduleMapPullbackAlong_isIso (a : U ⟶ V) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) [IsIso φ] :
    IsIso (MapSlicePullback.moduleMapPullbackAlong a φ) := by
  unfold MapSlicePullback.moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  simp only [Iso.homCongr_apply]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition
