import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback

/-! # Hom Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf

noncomputable section

/-! Actual module maps after base change form a presheaf on schemes over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def moduleHomPresheaf (M N : X.Modules) : (Over X)ᵒᵖ ⥤ Type u where
  obj U := (Scheme.Modules.pullback U.unop.hom).obj M ⟶ (Scheme.Modules.pullback U.unop.hom).obj N
  map f := TypeCat.ofHom (MapSlicePullback.moduleMapPullbackAlong f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact MapSlicePullback.moduleMapPullbackAlong_id U.unop φ
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact (MapSlicePullback.moduleMapPullbackAlong_comp g.unop f.unop φ).symm

theorem moduleMapPullbackAlong_of_map {U V : Over X} (a : U ⟶ V) {M N : X.Modules} (φ : M ⟶ N) :
    MapSlicePullback.moduleMapPullbackAlong a ((Scheme.Modules.pullback V.hom).map φ) =
      (Scheme.Modules.pullback U.hom).map φ := by
  unfold MapSlicePullback.moduleMapPullbackAlong
  rw [MapPullbackComposition.moduleMapPullbackComp_of_map, MapPullbackCongruence.moduleMapPullbackCongr_of_map]

def globalModuleMapSection (M N : X.Modules) (φ : M ⟶ N) : (moduleHomPresheaf M N).sections where
  val U := (Scheme.Modules.pullback U.unop.hom).map φ
  property f := moduleMapPullbackAlong_of_map f.unop φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf
