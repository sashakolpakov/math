import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates

/-! # Endpoint Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.EndpointTransport

noncomputable section

/-!
# Native pullback with equal affine coordinate maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback

/-- Equal endpoint coordinates in affine gluing give exactly the native scheme pullback. -/
theorem transported_eq_native {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {L : (Spec (CommRingCat.of A)).Modules} (i j : A →+* B) (k : B →+* C)
    (l m : A →+* C) (hl : k.comp i = l) (hm : k.comp j = m)
    (a : (Scheme.Modules.pullback (Affine.CechCoordinates.specMap i)).obj L ⟶
      (Scheme.Modules.pullback (Affine.CechCoordinates.specMap j)).obj L) :
    eqToHom (congrArg (fun r : A →+* C => (Scheme.Modules.pullback (Affine.CechCoordinates.specMap r)).obj L) hl.symm) ≫
        Affine.GluingPullback.geometricHom (CommRingCat.ofHom i) (CommRingCat.ofHom j) (CommRingCat.ofHom k) a ≫
          eqToHom (congrArg (fun r : A →+* C => (Scheme.Modules.pullback (Affine.CechCoordinates.specMap r)).obj L) hm) =
      Geometric.DescentEquations.nativePullback a (Affine.CechCoordinates.specMap k) (Affine.CechCoordinates.specMap l) (Affine.CechCoordinates.specMap m)
        (Affine.CechCoordinates.spec_comp_eq i k l hl) (Affine.CechCoordinates.spec_comp_eq j k m hm) := by
  subst l
  subst m
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have h := Affine.IntrinsicComparison.Intrinsic.geometricHom_eq_native
    (CommRingCat.ofHom i) (CommRingCat.ofHom j) (CommRingCat.ofHom k) a
  simpa only [← CommRingCat.ofHom_comp] using h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.EndpointTransport
