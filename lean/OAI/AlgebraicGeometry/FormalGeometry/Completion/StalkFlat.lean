import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Stalk Flat -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat.Construction

noncomputable section

/-! # Completion: the actual local-ring spectrum map is flat -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The canonical spectrum of a stalk is a flat localization on each actual affine chart. -/
theorem affineOpen_fromSpecStalk_flat {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) : Flat (hU.fromSpecStalk hx) := by
  unfold IsAffineOpen.fromSpecStalk
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/-- The actual localization morphism at a scheme point is flat. -/
theorem scheme_fromSpecStalk_flat (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  unfold Scheme.fromSpecStalk
  exact affineOpen_fromSpecStalk_flat _ _

/-- The local-ring spectrum is contained in every open neighborhood of its closed point. -/
theorem scheme_fromSpecStalk_preimage_eq_top (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) : X.fromSpecStalk x ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro y _
  have hy : X.fromSpecStalk x y ⤳ x :=
    (Scheme.range_fromSpecStalk (X := X) (x := x)).le ⟨y, rfl⟩
  exact hy.mem_open U.isOpen hx

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat.Construction
