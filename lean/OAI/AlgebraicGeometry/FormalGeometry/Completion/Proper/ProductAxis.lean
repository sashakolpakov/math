import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductConstancy

/-! # Product Axis -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis.Construction

noncomputable section

/-!
# Completion: the first product axis is the actual fiber at a section
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}} (A B : Over S) (b : S ⟶ B.left) (hb : b ≫ B.hom = 𝟙 _)

/-- The first product axis determined by the section of the second factor. -/
def properProductFirstAxisOver : A ⟶ ProductConstancy.Construction.properProductOver A B :=
  Over.homMk (pullback.lift (𝟙 A.left) (A.hom ≫ b) (by simp [Category.assoc, hb])) (by
    simp [ProductConstancy.Construction.properProductOver, Category.assoc, hb])

@[reassoc (attr := simp)]
theorem properProductFirstAxis_fst : (properProductFirstAxisOver A B b hb).left ≫
    pullback.fst A.hom B.hom = 𝟙 A.left := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem properProductFirstAxis_snd : (properProductFirstAxisOver A B b hb).left ≫
    pullback.snd A.hom B.hom = A.hom ≫ b := pullback.lift_snd _ _ _

/-- The axis is the fiber product above the section of the second factor. -/
theorem properProductFirstAxis_isPullback :
    IsPullback (properProductFirstAxisOver A B b hb).left A.hom
      (pullback.snd A.hom B.hom) b := by
  apply IsPullback.of_right (h₁₂ := pullback.fst A.hom B.hom)
    (v₁₃ := A.hom) (h₂₂ := B.hom)
    _ (properProductFirstAxis_snd A B b hb) (IsPullback.of_hasPullback A.hom B.hom)
  rw [properProductFirstAxis_fst, hb]
  exact IsPullback.of_id_fst

/-- The image of the axis is exactly the fiber over the image of the section. -/
theorem properProductFirstAxis_range :
    Set.range (properProductFirstAxisOver A B b hb).left =
      (pullback.snd A.hom B.hom) ⁻¹' Set.range b := by
  let h := properProductFirstAxis_isPullback A B b hb
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  rfl

variable {K : Type u} [Field K] (A B Z : Over (Spec (CommRingCat.of K)))
  (e : Spec (CommRingCat.of K) ⟶ A.left) (he : e ≫ A.hom = 𝟙 _)
  (b : Spec (CommRingCat.of K) ⟶ B.left) (hb : b ≫ B.hom = 𝟙 _)

/-- Equality along the actual first axis makes the constancy locus nonempty. -/
theorem properProductConstancySet_nonempty_of_firstAxis
    (f : ProductConstancy.Construction.properProductOver A B ⟶ Z)
    (h : properProductFirstAxisOver A B b hb ≫ f =
      properProductFirstAxisOver A B b hb ≫ ProductConstancy.Construction.properProductConstantMap A B Z e he f) :
    (ProductConstancy.Construction.properProductConstancySet A B Z e he f).Nonempty := by
  let x : Spec (CommRingCat.of K) := Nonempty.some inferInstance
  refine ⟨b x, (ProductConstancy.Construction.mem_properProductConstancySet A B Z e he f (b x)).mpr ?_⟩
  intro t ht
  have ht' : t ∈ Set.range (properProductFirstAxisOver A B b hb).left := by
    rw [properProductFirstAxis_range]
    exact ⟨x, ht.symm⟩
  obtain ⟨a, rfl⟩ := ht'
  refine ⟨(equalizer.lift (properProductFirstAxisOver A B b hb) h).left a, ?_⟩
  exact congrArg (fun k : A ⟶ ProductConstancy.Construction.properProductOver A B => k.left a)
    (equalizer.lift_ι (properProductFirstAxisOver A B b hb) h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis.Construction
