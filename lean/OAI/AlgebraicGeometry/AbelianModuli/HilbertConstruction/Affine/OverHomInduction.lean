import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality

/-! # Over Hom Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverHomInduction

noncomputable section

/-! Every morphism between affine test schemes over a fixed
base is induced by its actual coefficient homomorphism. This
eliminator retains dependent source base maps and Over morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert
universe u

theorem affineOverHom_ring_induction {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (f : Spec (.of R) ⟶ S)
    (Q : ∀ (g : Spec (.of A) ⟶ S), (Over.mk g ⟶ Over.mk f) → Prop)
    (h : ∀ φ : R →+* A, Q (Spec.map (CommRingCat.ofHom φ) ≫ f) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ))
    (g : Spec (.of A) ⟶ S) (b : Over.mk g ⟶ Over.mk f) : Q g b := by
  rcases b with ⟨q, r, w⟩
  change Spec (.of A) ⟶ Spec (.of R) at q
  change q ≫ f = g at w
  cases w
  have he : (⟨q, r, rfl⟩ : Over.mk (q ≫ f) ⟶ Over.mk f) =
      Over.homMk q rfl := Over.OverMorphism.ext rfl
  rw [he]
  have ht := h (Spec.preimage q).hom
  change Q (Spec.map (Spec.preimage q) ≫ f) (Over.homMk (Spec.map (Spec.preimage q)) rfl) at ht
  exact (Spec.map_preimage q) ▸ ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverHomInduction
