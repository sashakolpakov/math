import Mathlib
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius

/-! # Frobenius Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry

noncomputable section

/-!
# IntegralComparison: global q-Frobenius over a finite field

Iterate the actual scheme Frobenius from the proved Homomorphisms helper. Its action
on global functions is the p^a-power map, and over a field of cardinality
p^a the resulting scheme morphism is a morphism over that field.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (hp : p.Prime)

def iterate (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterate X hX n ≫ AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX

lemma iterate_appTop (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (s : Γ(X, ⊤)) :
    (FrobeniusGeometry.iterate p hp X hX n).appTop s = s ^ (p ^ n) := by
  induction n generalizing s with
  | zero => change s = s ^ (p ^ 0); simp
  | succ n ih =>
    change (FrobeniusGeometry.iterate p hp X hX n).appTop (s ^ p) = s ^ (p ^ (n + 1))
    rw [ih, ← pow_mul, ← pow_succ']

lemma hom_ext_appTop {X Y : Scheme.{u}} [IsAffine Y] {f g : X ⟶ Y} (h : f.appTop = g.appTop) : f = g := by
  apply (CategoryTheory.cancel_mono Y.toSpecΓ).mp
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h]

variable (k : Type u) [Field k] [CharP k p]

lemma spec_prime_zero : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := by
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).inv (CharP.cast_eq_zero k p)
  simpa only [map_natCast, map_zero] using h

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

include f in
lemma scheme_prime_zero : (p : Γ(X, ⊤)) = 0 :=
  AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p (spec_prime_zero p k) f

def qFrobenius (a : ℕ) : X ⟶ X := FrobeniusGeometry.iterate p hp X (scheme_prime_zero p k f) a

variable [Fintype k]

omit [CharP k p] in
lemma spec_global_fixed (a : ℕ) (hcard : Fintype.card k = p ^ a) (s : Γ(Spec (CommRingCat.of k), ⊤)) :
    s ^ (p ^ a) = s := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).injective
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s ^ (p ^ a)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom s
  rw [map_pow, ← hcard, FiniteField.pow_card]

lemma qFrobenius_over (a : ℕ) (hcard : Fintype.card k = p ^ a) : qFrobenius p hp k f a ≫ f = f := by
  apply hom_ext_appTop
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (FrobeniusGeometry.iterate p hp X (scheme_prime_zero p k f) a).appTop (f.appTop s) = f.appTop s
  rw [iterate_appTop, ← map_pow, spec_global_fixed p k a hcard]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry
