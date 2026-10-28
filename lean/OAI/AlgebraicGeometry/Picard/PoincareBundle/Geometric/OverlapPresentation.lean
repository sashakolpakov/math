import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCoordinateChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapInvariant

/-! # Overlap Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapPresentation

noncomputable section

/-!
# Invariants in any isomorphic presentation of the actual overlap
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapImage OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X)
  (h : p ≫ f = q ≫ f) (r : W ⟶ Z) [IsIso r] (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)
  (p' q' : W ⟶ X) (h' : p' ≫ f = q' ≫ f)
  (σ' : (Scheme.Modules.pullback p').obj M ≅ (Scheme.Modules.pullback q').obj M)
  (hp : r ≫ p = p') (hq : r ≫ q = q') (hσ : HEq (OverlapGluing.extendedGluing p q r M σ) σ')

/-- The invariant in the chosen overlap coordinates is the original actual invariant sheaf. -/
def invariantIso : CechInvariant.invariantSheaf f p' q' h' M σ' ≅ CechInvariant.invariantSheaf f p q h M σ :=
  (CechCoordinateChange.invariantIso f (OverlapImage.liftedRelation f p q h r) h' M
    (OverlapGluing.extendedGluing p q r M σ) σ' hp hq hσ).symm ≪≫
      OverlapInvariant.invariantIso f p q h r M σ

include hp hq hσ in
/-- Effectivity in the chosen coordinates is equivalent to effectivity on the original overlap. -/
theorem comparison_isIso_iff :
    IsIso (CechInvariant.comparison f p' q' h' M σ') ↔ IsIso (CechInvariant.comparison f p q h M σ) :=
  (CechCoordinateChange.comparison_isIso_iff f (OverlapImage.liftedRelation f p q h r) h' M
    (OverlapGluing.extendedGluing p q r M σ) σ' hp hq hσ).symm.trans
      (OverlapInvariant.comparison_isIso_iff f p q h r M σ)

/-- The chosen coordinate identification preserves the canonical comparison morphism. -/
theorem comparison_fac :
    (Scheme.Modules.pullback f).map (invariantIso f p q h r M σ p' q' h' σ' hp hq hσ).hom ≫
      CechInvariant.comparison f p q h M σ = CechInvariant.comparison f p' q' h' M σ' := by
  let e := CechCoordinateChange.invariantIso f (OverlapImage.liftedRelation f p q h r) h' M
    (OverlapGluing.extendedGluing p q r M σ) σ' hp hq hσ
  change (Scheme.Modules.pullback f).map (e.inv ≫
    (OverlapInvariant.invariantIso f p q h r M σ).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc,
    OverlapInvariant.comparison_commutes f p q h r M σ,
    ← CechCoordinateChange.comparison_fac f (OverlapImage.liftedRelation f p q h r) h' M
      (OverlapGluing.extendedGluing p q r M σ) σ' hp hq hσ]
  change (Scheme.Modules.pullback f).map e.inv ≫
    ((Scheme.Modules.pullback f).map e.hom ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, e.inv_hom_id, (Scheme.Modules.pullback f).map_id]
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapPresentation
