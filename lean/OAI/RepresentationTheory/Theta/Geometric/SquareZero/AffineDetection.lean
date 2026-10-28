import OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearDetection
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Detection -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineDetection

noncomputable section

/-! Morphisms from a split square-zero scheme to an affine scheme are
detected by their actual complex dual-number linear quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M]

theorem squareZero_affine_maps_ext (X : Scheme) [IsAffine X]
    (f g : Spec (.of (TrivSqZeroExt ℂ M)) ⟶ X)
    (h : ∀ l : M →ₗ[ℂ] ℂ,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom) ≫ f =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom) ≫ g) : f = g := by
  let a : Γ(X, ⊤) ⟶ CommRingCat.of (TrivSqZeroExt ℂ M) := Spec.preimage (f ≫ X.isoSpec.hom)
  let b : Γ(X, ⊤) ⟶ CommRingCat.of (TrivSqZeroExt ℂ M) := Spec.preimage (g ≫ X.isoSpec.hom)
  have ha : Spec.map a = f ≫ X.isoSpec.hom := Spec.map_preimage _
  have hb : Spec.map b = g ≫ X.isoSpec.hom := Spec.map_preimage _
  have hlin (l : M →ₗ[ℂ] ℂ) :
      a ≫ CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom =
        b ≫ CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha, hb, ← Category.assoc, ← Category.assoc, h l]
  have hab : a = b := CommRingCat.hom_ext
    (LinearDetection.squareZero_ring_maps_ext a.hom b.hom (fun l => congrArg CommRingCat.Hom.hom (hlin l)))
  apply (cancel_mono X.isoSpec.hom).mp
  exact ha.symm.trans ((congrArg Spec.map hab).trans hb)

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineDetection
