import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic

/-! # Frobenius -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction

/-!
# Homomorphisms: construction of scheme Frobenius

Result-specific foundations for Homomorphisms. No statement stub is imported.
Characteristic is expressed by `p = 0` in global sections; this also handles
empty schemes and the zero ring of sections on the empty open set.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) (hp : p.Prime)

/-- The p-power ring homomorphism, including the zero ring. -/
def powerRingHom (R : Type u) [CommRing R] (hR : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' := fun x y => mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    simpa only [hR, zero_mul, add_zero] using hr

@[simp]
theorem powerRingHom_apply (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (x : R) : powerRingHom p hp R hR x = x ^ p := rfl

theorem section_prime_eq_zero (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  have h := congrArg (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) hX
  simpa only [map_natCast, map_zero] using h

/-- Absolute Frobenius on the underlying ringed space. -/
def ringedFrobenius (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := {
    app := fun U => CommRingCat.ofHom
      (powerRingHom p hp Γ(X, U.unop) (section_prime_eq_zero p X hX U.unop))
    naturality := by
      intro U V f
      ext x
      exact (map_pow (X.presheaf.map f).hom x p).symm
  }

theorem ringedFrobenius_stalk_apply (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) (x : X) (a : X.presheaf.stalk x) :
    (ringedFrobenius p hp X hX).stalkMap x a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  erw [PresheafedSpace.stalkMap_germ_apply]
  exact map_pow (X.presheaf.germ U x hxU).hom s p

/-- Absolute Frobenius as a morphism of schemes. -/
def absoluteFrobenius (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X where
  toHom := ringedFrobenius p hp X hX
  prop x := {
    map_nonunit := by
      intro a ha
      have ha' : IsUnit (a ^ p) :=
        (ringedFrobenius_stalk_apply p hp X hX x a) ▸ ha
      exact (isUnit_pow_iff hp.ne_zero).mp ha'
  }

@[simp]
theorem absoluteFrobenius_apply (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) (x : X) :
    absoluteFrobenius p hp X hX x = x := rfl

@[simp]
theorem absoluteFrobenius_app (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) (s : Γ(X, U)) :
    (absoluteFrobenius p hp X hX).app U s = s ^ p := rfl

/-- Scheme Frobenius is natural, without any perfectness hypothesis. -/
theorem absoluteFrobenius_naturality {X Y : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) :
    absoluteFrobenius p hp X hX ≫ f = f ≫ absoluteFrobenius p hp Y hY := by
  apply Scheme.Hom.ext (by rfl)
  intro U
  change (f.app U ≫ (absoluteFrobenius p hp X hX).app (f ⁻¹ᵁ U)) ≫
    X.presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) =
      (absoluteFrobenius p hp Y hY).app U ≫ f.app U
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  exact (map_pow (f.app U).hom s p).symm

/-- Characteristic p propagates along a scheme morphism. -/
theorem prime_eq_zero_of_map {X Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) : (p : Γ(X, ⊤)) = 0 := by
  have h := congrArg f.appTop hY
  simpa only [map_natCast, map_zero] using h

/-- Every scheme over Spec F_p satisfies the characteristic condition. -/
theorem prime_eq_zero_of_overFp
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (ZMod p))) :
    (p : Γ(X, ⊤)) = 0 := by
  apply prime_eq_zero_of_map p (f := f)
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv
    (ZMod.natCast_self p)
  simpa only [map_natCast, map_zero] using h

open _root_.CategoryTheory.Limits

/-- The Frobenius twist is the actual scheme-theoretic base change. -/
noncomputable def frobeniusTwist {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) : Over S :=
  Over.mk (pullback.snd A.hom (absoluteFrobenius p hp S hS))

/-- Relative Frobenius is induced by the naturality square. -/
noncomputable def relativeFrobenius {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) :
    A ⟶ frobeniusTwist p hp hS A :=
  Over.homMk
    (pullback.lift
      (absoluteFrobenius p hp A.left (prime_eq_zero_of_map p hS A.hom))
      A.hom (absoluteFrobenius_naturality p hp _ hS A.hom))
    (pullback.lift_snd _ _ _)

/-- Relative and base Frobenius compose to absolute Frobenius. -/
theorem relativeFrobenius_comp_fst {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) :
    (relativeFrobenius p hp hS A).left ≫
      pullback.fst A.hom (absoluteFrobenius p hp S hS) =
        absoluteFrobenius p hp A.left (prime_eq_zero_of_map p hS A.hom) := by
  exact pullback.lift_fst _ _ _

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction
