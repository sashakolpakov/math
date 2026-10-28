import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Flat.Localization

/-! # Local Spectra -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.LocalSpectra

noncomputable section

/-! Canonical local-spectrum morphisms are flat, and flatness can be
recovered before postcomposition with a scheme monomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem flat_affine_fromSpecStalk {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) : Flat (hU.fromSpecStalk hx) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let := hU.isLocalization_stalk ⟨x, hx⟩
  have hg : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    change Module.Flat Γ(X, U) (X.presheaf.stalk x)
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact inferInstanceAs (Flat (Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec))

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  exact flat_affine_fromSpecStalk hU x hxU

theorem flat_of_comp_mono {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono g] [Flat (f ≫ g)] : Flat f := by
  let P : MorphismProperty Scheme.{u} := @Flat.{u}
  let : P.IsStableUnderBaseChange := Flat.isStableUnderBaseChange
  exact P.of_postcomp (W' := MorphismProperty.monomorphisms Scheme.{u})
    f g inferInstance inferInstance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.LocalSpectra
