import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductMap

/-! # Cover Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverBaseChange.Construction

noncomputable section

/-! The actual base change of a finite etale product cover is again such a product cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S A B T C : Scheme.{u}} (p : A ⟶ S) (q : B ⟶ S)
  (t : T ⟶ pullback p q) (h : C ⟶ B)

/-- The literal finite cover of the product after changing the second factor. -/
def productCoverBaseChangeMap :
    pullback (t ≫ pullback.snd p q) h ⟶ pullback p (h ≫ q) :=
  pullback.map _ _ _ _ t (𝟙 C) (𝟙 B) (by simp) (by simp) ≫
    (pullbackLeftPullbackSndIso p q h).hom

@[reassoc]
theorem productCoverBaseChangeMap_snd :
    productCoverBaseChangeMap p q t h ≫ pullback.snd p (h ≫ q) =
      pullback.snd (t ≫ pullback.snd p q) h := by
  simp [productCoverBaseChangeMap, pullbackLeftPullbackSndIso_hom_snd]

@[reassoc]
theorem productCoverBaseChangeMap_fst :
    productCoverBaseChangeMap p q t h ≫ pullback.fst p (h ≫ q) =
      pullback.fst (t ≫ pullback.snd p q) h ≫ t ≫ pullback.fst p q := by
  simp [productCoverBaseChangeMap, pullbackLeftPullbackSndIso_hom_fst]

theorem productCoverBaseChangeSquare :
    IsPullback
      (pullback.map (t ≫ pullback.snd p q) h (pullback.snd p q) h
        t (𝟙 C) (𝟙 B) (by simp) (by simp))
      (pullback.fst (t ≫ pullback.snd p q) h)
      (pullback.fst (pullback.snd p q) h) t := by
  refine .of_right (t := (IsPullback.of_hasPullback (pullback.snd p q) h).flip) ?_ ?_
  · simpa using (IsPullback.of_hasPullback (t ≫ pullback.snd p q) h).flip
  · simp

theorem productCoverBaseChangeMap_finite [IsFinite t] :
    IsFinite (productCoverBaseChangeMap p q t h) := by
  have : IsFinite (pullback.map (t ≫ pullback.snd p q) h (pullback.snd p q) h
      t (𝟙 C) (𝟙 B) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (productCoverBaseChangeSquare p q t h).flip
      inferInstance
  unfold productCoverBaseChangeMap
  infer_instance

theorem productCoverBaseChangeMap_etale [Etale t] :
    Etale (productCoverBaseChangeMap p q t h) := by
  have : Etale (pullback.map (t ≫ pullback.snd p q) h (pullback.snd p q) h
      t (𝟙 C) (𝟙 B) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (P := @Etale) (productCoverBaseChangeSquare p q t h).flip
      inferInstance
  unfold productCoverBaseChangeMap
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverBaseChange.Construction
