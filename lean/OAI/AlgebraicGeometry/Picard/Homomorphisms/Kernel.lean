import OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

noncomputable def kernelScheme {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) : Over S := equalizer q 1

noncomputable def kernelInclusion {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) : kernelScheme q ⟶ A := equalizer.ι q 1

set_option backward.isDefEq.respectTransparency.types false in
theorem kernelScheme_universal {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) (T : Over S) (a : T ⟶ A) :
    a ≫ q = 1 ↔ ∃! k : T ⟶ kernelScheme q, k ≫ kernelInclusion q = a := by
  constructor
  · intro ha
    have heq : a ≫ q = a ≫ (1 : A ⟶ B) := by simpa using ha
    refine ⟨equalizer.lift a heq, equalizer.lift_ι a heq, ?_⟩
    intro k hk
    apply equalizer.hom_ext
    exact hk.trans (equalizer.lift_ι a heq).symm
  · rintro ⟨k, hk, _⟩
    erw [← hk, Category.assoc, kernelInclusion, equalizer.condition]
    exact (Category.assoc k (kernelInclusion q) (1 : A ⟶ B)).symm.trans
      (MonObj.comp_one (M := B) (k ≫ kernelInclusion q))

set_option backward.isDefEq.respectTransparency.types false in
theorem kernelScheme_isPullback {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) :
    IsPullback (kernelInclusion q) (toUnit (kernelScheme q)) q η[B] := by
  have hcond : kernelInclusion q ≫ q = toUnit (kernelScheme q) ≫ η[B] := by
    change equalizer.ι q 1 ≫ q = 1
    rw [equalizer.condition]
    simp
  apply IsPullback.of_isLimit' ⟨hcond⟩
  apply PullbackCone.IsLimit.mk _
    (fun s => equalizer.lift s.fst (by
      rw [s.condition]
      have hs : s.snd = s.fst ≫ toUnit A := toUnit_unique _ _
      rw [hs, Category.assoc]
      rfl))
  · intro s
    exact equalizer.lift_ι _ _
  · intro s
    exact toUnit_unique _ _
  · intro s m hm₁ _
    apply equalizer.hom_ext
    exact hm₁.trans (equalizer.lift_ι _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem kernelScheme_finiteLocallyFree {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) (hq : Quotient.Construction.FiniteLocallyFreeHom q.left) :
    Quotient.Construction.FiniteLocallyFreeHom (kernelScheme q).hom := by
  have H := (kernelScheme_isPullback q).map (Over.forget S)
  change IsPullback (kernelInclusion q).left (kernelScheme q).hom q.left η[B].left at H
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H hq.1,
    MorphismProperty.of_isPullback (P := @Flat) H hq.2.1,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H hq.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
instance kernelInclusion_closedImmersion {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    [IsSeparated B.hom] (q : A ⟶ B) : IsClosedImmersion (kernelInclusion q).left :=
  inferInstanceAs (IsClosedImmersion (equalizer.ι q 1).left)

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction
