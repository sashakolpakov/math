import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Yoneda

/-! # Corepresentable Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableDescent.Construction

noncomputable section

/-!
# Completion: canonical coaction on an affine local representative

This is the algebra-side form of the representative descent construction.
It gives the actual coaction and verifies its counit and compatibility laws.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ Type w)
  {Y : D} (rep : (R ⋙ F).CorepresentableBy Y)

/-- The actual coaction determined by the universal section and the unit. -/
def corepresentableDescentCoaction : Y ⟶ L.obj (R.obj Y) :=
  rep.homEquiv.symm (F.map (adj.unit.app (R.obj Y)) (rep.homEquiv (𝟙 Y)))

theorem corepresentableDescentCoaction_section :
    rep.homEquiv (corepresentableDescentCoaction adj F rep) =
      F.map (adj.unit.app (R.obj Y)) (rep.homEquiv (𝟙 Y)) :=
  rep.homEquiv.apply_symm_apply _

theorem corepresentableDescentCoaction_pullback :
    F.map (R.map (corepresentableDescentCoaction adj F rep)) (rep.homEquiv (𝟙 Y)) =
      F.map (adj.unit.app (R.obj Y)) (rep.homEquiv (𝟙 Y)) := by
  exact (rep.homEquiv_eq (corepresentableDescentCoaction adj F rep)).symm.trans
    (corepresentableDescentCoaction_section adj F rep)

theorem corepresentableDescentCoaction_counit :
    corepresentableDescentCoaction adj F rep ≫ adj.counit.app Y = 𝟙 Y := by
  apply rep.homEquiv.injective
  erw [rep.homEquiv_comp, corepresentableDescentCoaction_section adj F rep]
  change F.map (R.map (adj.counit.app Y))
    (F.map (adj.unit.app (R.obj Y)) (rep.homEquiv (𝟙 Y))) = _
  erw [← Functor.map_comp_apply, adj.right_triangle_components]
  simp

theorem corepresentableDescentCoaction_coassoc :
    corepresentableDescentCoaction adj F rep ≫ L.map (adj.unit.app (R.obj Y)) =
      corepresentableDescentCoaction adj F rep ≫
        L.map (R.map (corepresentableDescentCoaction adj F rep)) := by
  let a := corepresentableDescentCoaction adj F rep
  let s := rep.homEquiv (𝟙 Y)
  apply rep.homEquiv.injective
  erw [rep.homEquiv_comp, rep.homEquiv_comp, corepresentableDescentCoaction_section adj F rep]
  change F.map (R.map (L.map (adj.unit.app (R.obj Y))))
      (F.map (adj.unit.app (R.obj Y)) s) =
    F.map (R.map (L.map (R.map a))) (F.map (adj.unit.app (R.obj Y)) s)
  calc
    _ = F.map (adj.unit.app (R.obj (L.obj (R.obj Y))))
        (F.map (adj.unit.app (R.obj Y)) s) := by
      erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      exact congrArg (fun g => F.map g s) (adj.unit.naturality (adj.unit.app (R.obj Y))).symm
    _ = F.map (adj.unit.app (R.obj (L.obj (R.obj Y)))) (F.map (R.map a) s) := by
      rw [corepresentableDescentCoaction_pullback adj F rep]
    _ = _ := by
      erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      exact congrArg (fun g => F.map g s) (adj.unit.naturality (R.map a))

/-- The local algebra representative carries the canonical checked descent coalgebra. -/
def corepresentableDescentCoalgebra : adj.toComonad.Coalgebra where
  A := Y
  a := corepresentableDescentCoaction adj F rep
  counit := corepresentableDescentCoaction_counit adj F rep
  coassoc := corepresentableDescentCoaction_coassoc adj F rep

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableDescent.Construction
