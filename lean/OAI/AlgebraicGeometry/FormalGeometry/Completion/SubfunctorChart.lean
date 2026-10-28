import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Subfunctor Chart -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorChart.Construction

noncomputable section

/-! A monomorphism with the proved pointwise factorization condition
gives an actual Cartesian representation of a subfunctor on a chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Category.{v} C] {A T M : C}
  (P : Subfunctor (yoneda.obj A)) (a : T ⟶ A) (m : M ⟶ T)
  (h : ∀ (U : C) (j : U ⟶ T), (j ≫ a) ∈ P.obj (op U) ↔ ∃ z : U ⟶ M, z ≫ m = j)

def subfunctorChartMap : yoneda.obj M ⟶ P.toFunctor where
  app U := TypeCat.ofHom (fun f => ⟨f ≫ (m ≫ a),
    P.map f.op ((h M m).mpr ⟨𝟙 M, Category.id_comp m⟩)⟩)
  naturality := by
    intro U V j
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact Category.assoc _ _ _

theorem subfunctorChart_isPullback [Mono m] :
    IsPullback (yoneda.map m) (subfunctorChartMap P a m h) (yoneda.map a) P.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro f
    exact Category.assoc _ _ _
  · intro f g hfg
    exact (cancel_mono m).mp hfg.1
  · intro j x hx
    change j ≫ a = x.val at hx
    have hp : (j ≫ a) ∈ P.obj U := hx.symm ▸ x.property
    obtain ⟨z, hz⟩ := (h U.unop j).mp hp
    refine ⟨z, hz, Subtype.ext ?_⟩
    change z ≫ (m ≫ a) = x.val
    rw [← Category.assoc, hz]
    exact hx

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorChart.Construction
