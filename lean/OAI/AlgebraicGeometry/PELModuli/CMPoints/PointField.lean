import Mathlib

/-! # Point Field -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PointField

noncomputable section

/-! A descended scheme point carries its actual coefficient-field map.
The complex descent triangle forces compatibility with the chosen base
embedding, so the subsequent q-adic specialization uses the same point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {B F : Type} [Field B] [Field F]
  (X : Over (Spec (.of B))) (p : Spec (.of F) ⟶ X.left)

def pointCoefficientEmbedding : B →+* F :=
  (Spec.preimage (p ≫ X.hom)).hom

theorem pointCoefficientEmbedding_spec :
    Spec.map (CommRingCat.ofHom (pointCoefficientEmbedding X p)) = p ≫ X.hom :=
  Spec.map_preimage _

theorem pointCoefficientEmbedding_compatible
    (κ : B →+* ℂ) (σ : F →+* ℂ) (pC : Spec (.of ℂ) ⟶ X.left)
    (hp : Spec.map (CommRingCat.ofHom σ) ≫ p = pC)
    (hC : pC ≫ X.hom = Spec.map (CommRingCat.ofHom κ)) :
    σ.comp (pointCoefficientEmbedding X p) = κ := by
  apply congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of ℂ => f.hom)
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (pointCoefficientEmbedding X p) ≫ CommRingCat.ofHom σ) = _
  rw [Spec.map_comp, pointCoefficientEmbedding_spec, ← Category.assoc, hp, hC]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PointField
