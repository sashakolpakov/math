import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Linear Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LinearAdjunction

noncomputable section

/-!
# IntegralComparison: coefficient linearity of left adjoints and their Hom equivalences
-/

open _root_.CategoryTheory

universe u v u' v' t

variable (R : Type t) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Linear R]

include adj in
theorem left_linear : F.Linear R where
  map_smul {X Y} f r := by
    apply (adj.homEquiv X (F.obj Y)).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_smul, Linear.comp_smul]
    exact (adj.unit.naturality (r • f)).symm.trans
      ((Linear.smul_comp _ _ _ r f (adj.unit.app Y)).trans
        (congrArg (fun g => r • g) (adj.unit.naturality f)))

def homLinearEquiv [F.Additive] (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  { adj.homEquiv X Y with
    map_add' := (adj.homAddEquiv X Y).map_add
    map_smul' := by
      intro r f
      change adj.homEquiv X Y (r • f) = r • adj.homEquiv X Y f
      rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_smul, Linear.comp_smul] }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LinearAdjunction
