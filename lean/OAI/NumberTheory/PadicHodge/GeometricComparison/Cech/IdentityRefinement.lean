import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.PullbackProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement

/-! # Identity Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IdentityRefinement.CechIdentityRefinement

noncomputable section

/-! Pullback by the identity scheme map, followed by an actual
cover refinement, is the original nonempty Cech refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (R : Type) [CommRing R] (X : Scheme.{0})
  {ι κ : Type} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)
  (b : P ⟶ (Image.CechImage.functor R (𝟙 X)).obj P)
  (hb : ∀ W, b.app W = 𝟙 _)

theorem coverLE (i : κ) : V i ≤ (𝟙 X) ⁻¹ᵁ U (r.f i) := leOfHom (r.φ i)

include hb in
theorem map : CechPullback.map R (𝟙 X) U V r.f (coverLE X U V r) b =
    NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply Pi.hom_ext
  intro t
  change Fin (q + 1) → κ at t
  let A := fun s : Fin (q + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))
  let B := fun s : Fin (q + 1) → κ => P.obj (op (∏ᶜ (V ∘ s)))
  let a := FormalCoproduct.powerMap r (Fin (q + 1))
  change (CechPullback.map R (𝟙 X) U V r.f (coverLE X U V r) b).f q ≫ Pi.π B t =
    Pi.lift (fun s => Pi.π A (r.f ∘ s) ≫ P.map (a.φ s).op) ≫ Pi.π B t
  erw [Pi.lift_comp_π]
  apply (PullbackProjection.CechPullback.map_f_π R (𝟙 X) U V r.f (coverLE X U V r) b q t).trans
  erw [hb, Category.id_comp]
  exact congrArg (fun c => Pi.π A (r.f ∘ t) ≫ P.map c)
    (congrArg Quiver.Hom.op (Subsingleton.elim
      (PullbackProjection.CechPullback.intersectionHom (𝟙 X) U V r.f (coverLE X U V r) q t) (a.φ t)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IdentityRefinement.CechIdentityRefinement
