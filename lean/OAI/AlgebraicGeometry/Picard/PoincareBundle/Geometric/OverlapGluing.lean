import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapNaturality
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Overlap Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing

noncomputable section

/-!
# The actual geometric gluing isomorphism on a changed overlap
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {P Q : C ⥤ D} (J : D ⥤ E) {P' Q' : C ⥤ E}
  (α : P ⋙ J ≅ P') (β : Q ⋙ J ≅ Q') (M : C) (σ : P.obj M ≅ Q.obj M)

/-- A geometric gluing isomorphism has the prescribed change-of-adjunction map. -/
def HasChangedHom (σ' : P'.obj M ≅ Q'.obj M) : Prop :=
  σ'.hom = Cech.AdjunctionChange.changedGluing α β (J.map σ.hom)

theorem hasChangedHom_of_eq (σ' : P'.obj M ≅ Q'.obj M)
    (h : σ' = PresentedMapNaturality.presentedIso J (α.app M) (β.app M) σ) :
    HasChangedHom J α β M σ σ' :=
  (congrArg Iso.hom h).trans (Category.assoc _ _ _).symm

end

universe u

variable {X Z W : Scheme.{u}} (p q : Z ⟶ X) (r : W ⟶ Z) (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- Pullback of the original gluing using the standard geometric composition isomorphisms. -/
def extendedGluing :
    (Scheme.Modules.pullback (r ≫ p)).obj M ≅ (Scheme.Modules.pullback (r ≫ q)).obj M :=
  PresentedMapNaturality.presentedIso (Scheme.Modules.pullback r)
    ((Scheme.Modules.pullbackComp r p).app M) ((Scheme.Modules.pullbackComp r q).app M) σ

theorem extendedGluing_eq : extendedGluing p q r M σ =
    PresentedMapNaturality.presentedIso (Scheme.Modules.pullback r)
      ((Scheme.Modules.pullbackComp r p).app M) ((Scheme.Modules.pullbackComp r q).app M) σ := rfl

/-- Its underlying map is exactly the transported gluing used by the invariant construction. -/
theorem extendedGluing_hasChangedHom :
    HasChangedHom (Scheme.Modules.pullback r) (Scheme.Modules.pullbackComp r p)
      (Scheme.Modules.pullbackComp r q) M σ (extendedGluing p q r M σ) :=
  hasChangedHom_of_eq (Scheme.Modules.pullback r) (Scheme.Modules.pullbackComp r p)
    (Scheme.Modules.pullbackComp r q) M σ (extendedGluing p q r M σ) (extendedGluing_eq p q r M σ)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing
