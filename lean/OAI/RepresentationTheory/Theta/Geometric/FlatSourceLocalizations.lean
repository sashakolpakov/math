import OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatCompositionDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Flat Source Localizations -/

namespace OAI.RepresentationTheory.Theta.Geometric.FlatSourceLocalizations

noncomputable section

/-! Flatness can be checked after localizing an ambient source at the
image of each point. This applies to the actual Picard comparison inclusion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem flat_stalkMap_of_flat_composition {X N Y : Scheme.{u}}
    (h : X ⟶ N) [Flat h] (g : N ⟶ Y) [Flat (h ≫ g)] (x : X) :
    (g.stalkMap (h x)).hom.Flat := by
  let a : Y.presheaf.stalk (g (h x)) →+* N.presheaf.stalk (h x) := (g.stalkMap (h x)).hom
  let b : N.presheaf.stalk (h x) →+* X.presheaf.stalk x := (h.stalkMap x).hom
  have hb : b.Flat := Flat.stalkMap h x
  have hab : (b.comp a).Flat := by
    simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] using Flat.stalkMap (h ≫ g) x
  algebraize [a, b, b.comp a]
  have : Module.Flat (N.presheaf.stalk (h x)) (X.presheaf.stalk x) := hb
  have : Module.Flat (Y.presheaf.stalk (g (h x))) (X.presheaf.stalk x) := hab
  have : IsLocalHom (algebraMap (N.presheaf.stalk (h x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom b)
  have : Module.FaithfullyFlat (N.presheaf.stalk (h x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatCompositionDescent.Construction.flat_of_faithfullyFlat_composition (Y.presheaf.stalk (g (h x)))
    (N.presheaf.stalk (h x)) (X.presheaf.stalk x)

theorem flat_of_ambient_stalk_localizations {Z B Y : Scheme.{u}}
    (i : Z ⟶ B) (p : B ⟶ Y)
    (hloc : ∀ z : Z, Flat (pullback.fst i (B.fromSpecStalk (i z)) ≫ i ≫ p)) :
    Flat (i ≫ p) := by
  apply Flat.of_stalkMap
  intro z
  let j := B.fromSpecStalk (i z)
  have : Flat j := OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat.Construction.scheme_fromSpecStalk_flat B (i z)
  have : Flat (pullback.fst i j ≫ (i ≫ p)) := hloc z
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := j)
    z (IsLocalRing.closedPoint (B.presheaf.stalk (i z)))
    Scheme.fromSpecStalk_closedPoint.symm
  have h := flat_stalkMap_of_flat_composition (pullback.fst i j) (i ≫ p) w
  rwa [hw] at h

end

end OAI.RepresentationTheory.Theta.Geometric.FlatSourceLocalizations
