import OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatCompositionDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Scheme Flat Composition Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeFlatCompositionDescent.Construction

noncomputable section

/-! # Completion: flatness descends through an actual surjective flat scheme map -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Stalkwise faithful flatness descends flatness from the actual composite. -/
theorem scheme_flat_of_surjective_flat_composition {X N Y : Scheme.{u}}
    (h : X ⟶ N) [Surjective h] [Flat h] (g : N ⟶ Y) [Flat (h ≫ g)] : Flat g := by
  apply Flat.of_stalkMap
  intro n
  obtain ⟨x, rfl⟩ := h.surjective n
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
  exact FlatCompositionDescent.Construction.flat_of_faithfullyFlat_composition (Y.presheaf.stalk (g (h x)))
    (N.presheaf.stalk (h x)) (X.presheaf.stalk x)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeFlatCompositionDescent.Construction
