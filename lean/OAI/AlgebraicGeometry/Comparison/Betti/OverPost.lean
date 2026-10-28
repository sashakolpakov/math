import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.IsConnected

/-! # Over Post -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OverPost.RingedModules

/-! The functor on slices preserves their terminal objects and is therefore final. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (U : C)

theorem overPost_final : (Over.post (X := U) F).Final where
  out V := by
    let q : V ⟶ (Over.post (X := U) F).obj (Over.mk (𝟙 U)) :=
      Over.homMk V.hom (by
        change V.hom ≫ F.map (𝟙 U) = V.hom
        rw [F.map_id, Category.comp_id])
    let T : StructuredArrow V (Over.post (X := U) F) := StructuredArrow.mk q
    have hT : IsTerminal T := IsTerminal.ofUniqueHom
      (fun W => StructuredArrow.homMk (Over.homMk W.right.hom) (by
        apply Over.OverMorphism.ext
        exact Over.w W.hom))
      (fun W g => StructuredArrow.hom_ext _ _ (Over.mkIdTerminal.hom_ext _ _))
    exact CategoryTheory.isConnected_of_isTerminal _ hT

end OAI.AlgebraicGeometry.Comparison.Betti.OverPost.RingedModules
