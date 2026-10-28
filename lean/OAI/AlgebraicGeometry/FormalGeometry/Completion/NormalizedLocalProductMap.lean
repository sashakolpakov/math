import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFunctions

/-! # Normalized Local Product Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalProductMap.Construction

noncomputable section

/-! The actual normalized local family is a finite etale cover of the factor times its literal stalk base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] {A B T : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p]
  (q : B ⟶ Spec (CommRingCat.of K)) (t : T ⟶ pullback p q) [IsFinite t]
  (n : (t ≫ pullback.snd p q).normalization)

/-- The literal field-valued structure map of the actual normalization stalk spectrum. -/
def normalizedLocalBaseToField :
    Spec ((t ≫ pullback.snd p q).normalization.presheaf.stalk n) ⟶ Spec (CommRingCat.of K) :=
  (t ≫ pullback.snd p q).normalization.fromSpecStalk n ≫
    ((t ≫ pullback.snd p q).fromNormalization ≫ q)

/-- The source is exactly the actual normalized local family, with its original base map. -/
def normalizedLocalProductMap :
    pullback (t ≫ pullback.snd p q).toNormalization
      ((t ≫ pullback.snd p q).normalization.fromSpecStalk n) ⟶
        pullback p (normalizedLocalBaseToField p q t n) :=
  (pullback.congrHom (NormalizedProductMap.Construction.normalizedProductMap_snd p q t).symm rfl).hom ≫
    Product.CoverBaseChange.Construction.productCoverBaseChangeMap p ((t ≫ pullback.snd p q).fromNormalization ≫ q)
      (NormalizedProductMap.Construction.normalizedProductMap p q t) ((t ≫ pullback.snd p q).normalization.fromSpecStalk n)

@[reassoc]
theorem normalizedLocalProductMap_snd :
    normalizedLocalProductMap p q t n ≫ pullback.snd p (normalizedLocalBaseToField p q t n) =
      NormalizedLocalFunctions.Construction.normalizedLocalFamily (t ≫ pullback.snd p q) n := by
  simp [normalizedLocalProductMap, normalizedLocalBaseToField, NormalizedLocalFunctions.Construction.normalizedLocalFamily,
    Product.CoverBaseChange.Construction.productCoverBaseChangeMap_snd]

theorem normalizedLocalProductMap_finite
    [IsFinite (t ≫ pullback.snd p q).fromNormalization] :
    IsFinite (normalizedLocalProductMap p q t n) := by
  have : IsFinite (NormalizedProductMap.Construction.normalizedProductMap p q t) := NormalizedProductMap.Construction.normalizedProductMap_finite p q t
  have := Product.CoverBaseChange.Construction.productCoverBaseChangeMap_finite p ((t ≫ pullback.snd p q).fromNormalization ≫ q)
    (NormalizedProductMap.Construction.normalizedProductMap p q t) ((t ≫ pullback.snd p q).normalization.fromSpecStalk n)
  unfold normalizedLocalProductMap
  infer_instance

theorem normalizedLocalProductMap_etale [Etale t]
    [Etale (t ≫ pullback.snd p q).fromNormalization] :
    Etale (normalizedLocalProductMap p q t n) := by
  have : Etale (NormalizedProductMap.Construction.normalizedProductMap p q t) := NormalizedProductMap.Construction.normalizedProductMap_etale p q t
  have := Product.CoverBaseChange.Construction.productCoverBaseChangeMap_etale p ((t ≫ pullback.snd p q).fromNormalization ≫ q)
    (NormalizedProductMap.Construction.normalizedProductMap p q t) ((t ≫ pullback.snd p q).normalization.fromSpecStalk n)
  unfold normalizedLocalProductMap
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalProductMap.Construction
