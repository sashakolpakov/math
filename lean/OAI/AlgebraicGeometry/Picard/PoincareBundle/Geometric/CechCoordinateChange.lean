import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Cech Coordinate Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCoordinateChange

noncomputable section

/-!
# Equal overlap coordinate maps retain the actual geometric invariant
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) {p q p' q' : Z ⟶ X}
  (h : p ≫ f = q ≫ f) (h' : p' ≫ f = q' ≫ f) (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)
  (σ' : (Scheme.Modules.pullback p').obj M ≅ (Scheme.Modules.pullback q').obj M)

/-- Equal coordinates and the same transported gluing give canonically isomorphic invariants. -/
def invariantIso (hp : p = p') (hq : q = q') (hσ : HEq σ σ') :
    CechInvariant.invariantSheaf f p q h M σ ≅
      CechInvariant.invariantSheaf f p' q' h' M σ' := by
  subst p'
  subst q'
  cases eq_of_heq hσ
  exact Iso.refl _

/-- The coordinate identification retains the actual canonical comparison morphism. -/
theorem comparison_fac (hp : p = p') (hq : q = q') (hσ : HEq σ σ') :
    (Scheme.Modules.pullback f).map (invariantIso f h h' M σ σ' hp hq hσ).hom ≫
      CechInvariant.comparison f p' q' h' M σ' =
    CechInvariant.comparison f p q h M σ := by
  subst p'
  subst q'
  cases eq_of_heq hσ
  change (Scheme.Modules.pullback f).map (𝟙 _) ≫ _ = _
  rw [(Scheme.Modules.pullback f).map_id]
  exact Category.id_comp _

/-- Invertibility is unchanged by equal coordinate maps and the same gluing. -/
theorem comparison_isIso_iff (hp : p = p') (hq : q = q') (hσ : HEq σ σ') :
    IsIso (CechInvariant.comparison f p q h M σ) ↔
      IsIso (CechInvariant.comparison f p' q' h' M σ') := by
  subst p'
  subst q'
  cases eq_of_heq hσ
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCoordinateChange
