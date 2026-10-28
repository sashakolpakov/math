import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalLifts
import Mathlib.Geometry.RingedSpace.SheafedSpace

/-! # Local Detection Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalDetectionOf.LocalDetection

/-!
# TorsionQuotient: detecting equality of scheme maps on local test rings

The maps from spectra of all source stalks jointly detect scheme morphisms.
This lets a local-ring infinitesimal argument prove a global uniqueness
statement without assuming an affine target.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem hom_ext_of_fromSpecStalk {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have hb : f.base = g.base := by
    ext x
    have hx := congrArg
      (fun z : Spec (X.presheaf.stalk x) ⟶ Y => z (IsLocalRing.closedPoint (X.presheaf.stalk x)))
      (h x)
    change f (X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x))) =
      g (X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x))) at hx
    simpa only [Scheme.fromSpecStalk_closedPoint] using hx
  have hs := SheafedSpace.hom_stalk_ext f.toLRSHom.toShHom g.toLRSHom.toShHom hb
    (fun x => by
      have he : (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm
          ⟨f x, ⟨f.stalkMap x, inferInstance⟩⟩ =
          (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm
          ⟨g x, ⟨g.stalkMap x, inferInstance⟩⟩ :=
        (Scheme.SpecMap_stalkMap_fromSpecStalk f).trans
          ((h x).trans (Scheme.SpecMap_stalkMap_fromSpecStalk g).symm)
      obtain ⟨_, he⟩ := SpecToEquivOfLocalRing_eq_iff.mp
        ((SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm.injective he)
      exact he)
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  exact congrArg (fun z => z.hom) hs

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalDetectionOf.LocalDetection
