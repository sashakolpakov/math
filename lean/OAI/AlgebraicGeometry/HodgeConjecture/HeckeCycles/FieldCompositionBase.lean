import Mathlib

/-! # Field Composition Base -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldCompositionBase.CM.Points

noncomputable section

/-! Explicit scheme maps for a composite of two field embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K L F : Type} [Field K] [Field L] [Field F]
  (α : K →+* L) (σ : L →+* F)

theorem spec_comp : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom α) =
    Spec.map (CommRingCat.ofHom (σ.comp α)) :=
  (Spec.map_comp (CommRingCat.ofHom α) (CommRingCat.ofHom σ)).symm

def compositeTestIso :
    Over.mk (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom α)) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (σ.comp α))) :=
  Over.isoMk (Iso.refl _) ((Category.id_comp
    (Spec.map (CommRingCat.ofHom (σ.comp α)))).trans (spec_comp α σ).symm)

def compositionTestMap :
    Over.mk (Spec.map (CommRingCat.ofHom (σ.comp α))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom α)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ)) (spec_comp α σ)

theorem compositionTestMap_left :
    (compositionTestMap α σ).left = Spec.map (CommRingCat.ofHom σ) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldCompositionBase.CM.Points
