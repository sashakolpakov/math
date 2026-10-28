import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso

/-! # Map Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MapComparison

/-! Equality of fiber comparisons transports normalization of an
actual product map without expanding either comparison construction. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ C)
    (n n' : F ⋙ G ≅ 𝟭 C) (h : n = n') {X : D}

include h in
theorem normalizedProductMap_comparison_congr (f : X ⟶ F.obj (G.obj X))
    (hf : G.map f ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)) :
    G.map f ≫ n'.hom.app (G.obj X) = 𝟙 (G.obj X) := by
  subst n'
  exact hf

theorem normalizedProductMap_map_congr (f g : X ⟶ F.obj (G.obj X)) (hfg : f = g)
    (hg : G.map g ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)) :
    G.map f ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X) := by
  subst g
  exact hg

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MapComparison
