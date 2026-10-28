import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Properties -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

theorem powerRingHom_integral (R : Type u) [CommRing R]
    (hR : (p : R) = 0) : (Frobenius.Construction.powerRingHom p hp R hR).IsIntegral := by
  intro x
  refine ⟨Polynomial.X ^ p - Polynomial.C x, Polynomial.monic_X_pow_sub_C x hp.ne_zero, ?_⟩
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Frobenius.Construction.powerRingHom]

instance absoluteFrobenius_affine (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) : IsAffineHom (Frobenius.Construction.absoluteFrobenius p hp X hX) where
  isAffine_preimage _ hU := hU

instance absoluteFrobenius_integral (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) : IsIntegralHom (Frobenius.Construction.absoluteFrobenius p hp X hX) where
  isIntegral_app U _ := powerRingHom_integral p hp Γ(X, U)
    (Frobenius.Construction.section_prime_eq_zero p X hX U)

instance absoluteFrobenius_surjective (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) : Surjective (Frobenius.Construction.absoluteFrobenius p hp X hX) where
  surj x := ⟨x, rfl⟩

theorem ringedFrobenius_stalk_injective (X : Scheme.{u}) [IsReduced X]
    (hX : (p : Γ(X, ⊤)) = 0) (x : X) :
    Function.Injective ((Frobenius.Construction.ringedFrobenius p hp X hX).stalkMap x) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply _root_.IsReduced.eq_zero
  refine ⟨p, ?_⟩
  erw [← Frobenius.Construction.ringedFrobenius_stalk_apply p hp X hX x (a - b)]
  exact ((Frobenius.Construction.ringedFrobenius p hp X hX).stalkMap x).hom.map_sub a b |>.trans
    (sub_eq_zero.mpr hab)

instance absoluteFrobenius_epi (X : Scheme.{u}) [IsReduced X]
    (hX : (p : Γ(X, ⊤)) = 0) : Epi (Frobenius.Construction.absoluteFrobenius p hp X hX) := by
  apply (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).epi_of_epi_map
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono
  · intro x
    exact ⟨x, rfl⟩
  · intro x
    exact ConcreteCategory.mono_of_injective _
      (ringedFrobenius_stalk_injective p hp X hX x)

instance absoluteFrobenius_universallyInjective (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) :
    UniversallyInjective (Frobenius.Construction.absoluteFrobenius p hp X hX) := by
  apply ((tfae_universallyInjective (Frobenius.Construction.absoluteFrobenius p hp X hX)).out 2 1).mp
  intro K _ g h he
  let hK := Frobenius.Construction.prime_eq_zero_of_map p hX g
  apply (cancel_epi (Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of K)) hK)).mp
  rw [Frobenius.Construction.absoluteFrobenius_naturality p hp hK hX g,
    Frobenius.Construction.absoluteFrobenius_naturality p hp hK hX h]
  exact he

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_integral {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) :
    IsIntegralHom (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  have hcomp : IsIntegralHom ((Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) := by
    rw [Frobenius.Construction.relativeFrobenius_comp_fst]
    infer_instance
  have hsep : IsSeparated (pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) :=
    IsSeparated.of_isAffineHom _
  exact @IsIntegralHom.of_comp A.left
    (pullback A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) A.left
    (Frobenius.Construction.relativeFrobenius p hp hS A).left
    (pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) hcomp hsep

instance relativeFrobenius_finite {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [LocallyOfFiniteType A.hom] :
    IsFinite (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  have hcomp : LocallyOfFiniteType ((Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (Frobenius.Construction.frobeniusTwist p hp hS A).hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (Frobenius.Construction.relativeFrobenius p hp hS A).left :=
    locallyOfFiniteType_of_comp _ (Frobenius.Construction.frobeniusTwist p hp hS A).hom
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_surjective {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) :
    Surjective (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  constructor
  intro y
  let π := pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)
  have : UniversallyInjective π :=
    MorphismProperty.pullback_fst (P := @UniversallyInjective)
      A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS) inferInstance
  refine ⟨π y, π.injective ?_⟩
  have h := congrArg (fun f : A.left ⟶ A.left => f (π y))
    (Frobenius.Construction.relativeFrobenius_comp_fst p hp hS A)
  exact h

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_universallyInjective {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) :
    UniversallyInjective (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  apply ((tfae_universallyInjective (Frobenius.Construction.relativeFrobenius p hp hS A).left).out 2 1).mp
  intro K _ g h he
  have hinj : ∀ (L : Type u) [Field L], Function.Injective
      (fun g : Spec (CommRingCat.of L) ⟶ A.left =>
        g ≫ Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom)) :=
    ((tfae_universallyInjective
    (Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom))).out 1 2).mp
      (absoluteFrobenius_universallyInjective p hp A.left _)
  apply hinj K
  let π := pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)
  let F := (Frobenius.Construction.relativeFrobenius p hp hS A).left
  have hF := Frobenius.Construction.relativeFrobenius_comp_fst p hp hS A
  calc
    g ≫ Frobenius.Construction.absoluteFrobenius p hp A.left _ = g ≫ (F ≫ π) :=
      congrArg (fun t => g ≫ t) hF.symm
    _ = (g ≫ F) ≫ π := (Category.assoc g F π).symm
    _ = (h ≫ F) ≫ π := congrArg (fun t => t ≫ π) he
    _ = h ≫ (F ≫ π) := Category.assoc h F π
    _ = h ≫ Frobenius.Construction.absoluteFrobenius p hp A.left _ :=
      congrArg (fun t => h ≫ t) hF

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties.Construction
