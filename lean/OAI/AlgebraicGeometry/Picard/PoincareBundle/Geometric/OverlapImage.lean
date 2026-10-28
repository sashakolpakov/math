import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapExtension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Overlap Image -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapImage

noncomputable section

/-!
# Standard geometric direct-image comparison after changing the overlap
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X)
  (h : p ≫ f = q ≫ f) (r : W ⟶ Z)

include h in
/-- The same projection relation on the changed overlap. -/
theorem liftedRelation : (r ≫ p) ≫ f = (r ≫ q) ≫ f :=
  (Category.assoc r p f).trans ((congrArg (fun z => r ≫ z) h).trans (Category.assoc r q f).symm)

/-- The comparison obtained by extending the overlap and then using actual composite pushforwards. -/
def compositeDirectImageIso :
    Scheme.Modules.pushforward (r ≫ p) ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (r ≫ q) ⋙ Scheme.Modules.pushforward f :=
  Cech.AdjunctionChange.changedRightIso (Scheme.Modules.pushforwardComp r p)
    (Scheme.Modules.pushforwardComp r q)
    (Cech.OverlapExtension.extendedRightIso
      (CechInvariant.directImageIso f p q h) (K := Scheme.Modules.pushforward r))

/-- This is precisely the standard comparison for the composite geometric projections. -/
theorem compositeDirectImageIso_eq :
    compositeDirectImageIso f p q h r =
      CechInvariant.directImageIso f (r ≫ p) (r ≫ q) (liftedRelation f p q h r) := by
  apply Iso.ext
  ext M U x
  simp [compositeDirectImageIso, Cech.AdjunctionChange.changedRightIso,
    Cech.OverlapExtension.extendedRightIso, CechInvariant.directImageIso]
  erw [eqToHom_map (TopologicalSpace.Opens.map r.base)]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapImage
