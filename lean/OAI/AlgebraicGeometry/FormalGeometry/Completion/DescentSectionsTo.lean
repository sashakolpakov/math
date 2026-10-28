import OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableDescent

/-! # Descent Sections To -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DescentSectionsTo.Construction

noncomputable section

/-!
# Completion: sections compatible with descent and morphisms of the canonical coalgebra

The coalgebra morphism condition is exactly equality of the two pullbacks
of a local section. This is the bridge from algebra descent to sheaf descent.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ Type w)

/-- Local sections whose two descent pullbacks agree. -/
def DescentSections (T : C) :=
  {x : F.obj (R.obj (L.obj T)) //
    F.map (adj.unit.app (R.obj (L.obj T))) x = F.map (R.map (L.map (adj.unit.app T))) x}

/-- Every original section pulls back to a compatible local section. -/
def sectionToDescent (T : C) (x : F.obj T) : DescentSections adj F T :=
  ⟨F.map (adj.unit.app T) x, by
    erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact congrArg (fun g => F.map g x) (adj.unit.naturality (adj.unit.app T))⟩

variable {Y : D} (rep : (R ⋙ F).CorepresentableBy Y) (T : C)

/-- Pulling back the canonical coaction agrees with restriction of the represented section. -/
theorem corepresentable_coaction_hom_section (g : Y ⟶ L.obj T) :
    rep.homEquiv (CorepresentableDescent.Construction.corepresentableDescentCoaction adj F rep ≫ L.map (R.map g)) =
      F.map (adj.unit.app (R.obj (L.obj T))) (rep.homEquiv g) := by
  erw [rep.homEquiv_comp, CorepresentableDescent.Construction.corepresentableDescentCoaction_section adj F rep]
  rw [rep.homEquiv_eq g]
  change F.map (R.map (L.map (R.map g)))
      (F.map (adj.unit.app (R.obj Y)) (rep.homEquiv (𝟙 Y))) =
    F.map (adj.unit.app (R.obj (L.obj T))) (F.map (R.map g) (rep.homEquiv (𝟙 Y)))
  erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun h => F.map h (rep.homEquiv (𝟙 Y))) (adj.unit.naturality (R.map g)).symm

/-- Morphisms out of the canonical coalgebra are exactly compatible local sections. -/
theorem corepresentable_coalgebra_condition_iff (g : Y ⟶ L.obj T) :
    (CorepresentableDescent.Construction.corepresentableDescentCoalgebra adj F rep).a ≫ adj.toComonad.map g =
        g ≫ ((Comonad.comparison adj).obj T).a ↔
      F.map (adj.unit.app (R.obj (L.obj T))) (rep.homEquiv g) =
        F.map (R.map (L.map (adj.unit.app T))) (rep.homEquiv g) := by
  change CorepresentableDescent.Construction.corepresentableDescentCoaction adj F rep ≫ L.map (R.map g) =
      g ≫ L.map (adj.unit.app T) ↔ _
  rw [← rep.homEquiv.injective.eq_iff]
  erw [corepresentable_coaction_hom_section adj F rep T g, rep.homEquiv_comp]
  rfl

/-- The actual bijection between coalgebra morphisms and sections satisfying the descent equality. -/
def corepresentableCoalgebraHomEquiv :
    (CorepresentableDescent.Construction.corepresentableDescentCoalgebra adj F rep ⟶ (Comonad.comparison adj).obj T) ≃
      DescentSections adj F T where
  toFun g := ⟨rep.homEquiv g.f, (corepresentable_coalgebra_condition_iff adj F rep T g.f).mp g.h⟩
  invFun x := {
    f := rep.homEquiv.symm x.val
    h := (corepresentable_coalgebra_condition_iff adj F rep T _).mpr (by
      erw [rep.homEquiv.apply_symm_apply]
      exact x.property) }
  left_inv g := by
    apply Comonad.Coalgebra.Hom.ext
    exact rep.homEquiv.symm_apply_apply g.f
  right_inv x := Subtype.ext (rep.homEquiv.apply_symm_apply x.val)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DescentSectionsTo.Construction
