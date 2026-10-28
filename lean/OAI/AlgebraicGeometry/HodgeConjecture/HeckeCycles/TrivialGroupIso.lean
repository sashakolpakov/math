import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Trivial Group Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TrivialGroupIso.CM

noncomputable section

/-! Group objects with exactly one point on every test object are
isomorphic through their actual unit morphisms. -/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (G H : Grp C)

def iso (hG : ∀ T : C, Subsingleton (T ⟶ G.X)) (hH : ∀ T : C, Subsingleton (T ⟶ H.X)) :
    G ≅ H := by
  let e : G.X ≅ H.X := {
    hom := 1
    inv := 1
    hom_inv_id := (hG G.X).elim _ _
    inv_hom_id := (hH H.X).elim _ _ }
  let : IsMonHom e.hom := inferInstanceAs (IsMonHom (toUnit G.X ≫ η[H.X]))
  exact Grp.mkIso' e

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TrivialGroupIso.CM
