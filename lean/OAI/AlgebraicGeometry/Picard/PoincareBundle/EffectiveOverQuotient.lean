import Mathlib.AlgebraicGeometry.Sites.Fpqc
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers

/-! # Effective Over Quotient -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient

/-! Effective quotient morphisms over the specified scheme base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v

section

variable {C : Type u} [Category.{v} C]

/-- Relations in the slice detect the underlying relations. -/
theorem over_coequalizes_left {S : C} {A B W : Over S}
    (f : A ⟶ B) (g : A ⟶ W)
    (hg : ∀ {T : Over S} (x y : T ⟶ A),
      x ≫ f = y ≫ f → x ≫ g = y ≫ g) :
    ∀ {T : C} (x y : T ⟶ A.left),
      x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left := by
  intro T x y hxy
  let T' : Over S := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hxy])
  exact congrArg Over.Hom.left (hg x' y' (Over.OverMorphism.ext hxy))

/-- Effective epimorphisms of the underlying objects remain effective
epimorphisms in a slice category. -/
theorem effectiveEpi_over_of_left {S : C} {A B : Over S}
    (f : A ⟶ B) [EffectiveEpi f.left] : EffectiveEpi f := by
  constructor
  refine ⟨{
    desc := fun {W} g hg => ?_
    fac := ?_
    uniq := ?_
  }⟩
  · have hrel : ∀ {T : C} (x y : T ⟶ A.left),
        x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left :=
      over_coequalizes_left f g hg
    let d := EffectiveEpi.desc f.left g.left hrel
    refine Over.homMk d ?_
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, EffectiveEpi.fac, Over.w g, Over.w f]
  · intro W g hg
    apply Over.OverMorphism.ext
    dsimp
    apply EffectiveEpi.fac
    exact over_coequalizes_left f g hg
  · intro W g hg m hm
    apply Over.OverMorphism.ext
    exact EffectiveEpi.uniq f.left g.left (over_coequalizes_left f g hg)
      m.left (congrArg Over.Hom.left hm)

end

/-- An affine flat surjection is an effective quotient over its actual scheme base. -/
theorem affine_effective {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] : EffectiveEpi f :=
  effectiveEpi_over_of_left f

/-- The square of an affine flat surjection is an effective quotient over the same base. -/
theorem tensor_effective {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] : EffectiveEpi (f ⊗ₘ f) := by
  have : IsAffineHom (f ⊗ₘ f).left := Product.Covers.tensorAffine f f
  have : Flat (f ⊗ₘ f).left := Product.Covers.tensorFlat f f
  have : Surjective (f ⊗ₘ f).left := Product.Covers.tensorSurjective f f
  exact affine_effective (f ⊗ₘ f)

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient
