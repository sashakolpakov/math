import OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusFixedLifts

/-! # Finite Field Lift -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFieldLift

noncomputable section

/-!
# Canonical lifting of finite-field maps through nil ideals

The Frobenius-fixed subring isomorphism constructs the lift. Uniqueness comes
from the fact that every element of the finite source satisfies x^q = x.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusFixedLifts

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

def degree : ℕ+ := (FiniteField.card k p).choose

omit [Fact p.Prime] in
theorem degree_card : Fintype.card k = p ^ (degree p k : ℕ) :=
  (FiniteField.card k p).choose_spec.2

variable {R S : Type*} [CommRing R] [CharP R p] [CommRing S] [CharP S p]

def toFixed (κ : k →+* S) : k →+* FrobeniusFixedLifts.fixedSubring p (degree p k) S where
  toFun a := ⟨κ a, by
    change κ a ^ (p ^ (degree p k : ℕ)) = κ a
    rw [← degree_card, ← map_pow, FiniteField.pow_card]⟩
  map_zero' := Subtype.ext (map_zero κ)
  map_one' := Subtype.ext (map_one κ)
  map_add' a b := Subtype.ext (map_add κ a b)
  map_mul' a b := Subtype.ext (map_mul κ a b)

variable (f : R →+* S) (hsurj : Function.Surjective f)
  (hnil : ∀ r : R, f r = 0 → IsNilpotent r)

def lift (κ : k →+* S) : k →+* R :=
  (FrobeniusFixedLifts.fixedSubring p (degree p k) R).subtype.comp
    ((FrobeniusFixedLifts.fixedEquiv p (degree p k) (degree p k).pos f hnil hsurj).symm.toRingHom.comp (toFixed p k κ))

theorem lift_spec (κ : k →+* S) (a : k) : f (lift p k f hsurj hnil κ a) = κ a :=
  congrArg Subtype.val
    ((FrobeniusFixedLifts.fixedEquiv p (degree p k) (degree p k).pos f hnil hsurj).apply_symm_apply (toFixed p k κ a))

theorem lift_pow (κ : k →+* S) (a : k) :
    lift p k f hsurj hnil κ a ^ (p ^ (degree p k : ℕ)) = lift p k f hsurj hnil κ a :=
  ((FrobeniusFixedLifts.fixedEquiv p (degree p k) (degree p k).pos f hnil hsurj).symm (toFixed p k κ a)).property

theorem lift_unique (κ : k →+* S) (g : k →+* R) (hg : ∀ a, f (g a) = κ a) :
    g = lift p k f hsurj hnil κ := by
  apply RingHom.ext
  intro a
  have hgpow : g a ^ (p ^ (degree p k : ℕ)) = g a := by
    rw [← degree_card, ← map_pow, FiniteField.pow_card]
  let x : FrobeniusFixedLifts.fixedSubring p (degree p k) R := ⟨g a, hgpow⟩
  let y : FrobeniusFixedLifts.fixedSubring p (degree p k) R :=
    ⟨lift p k f hsurj hnil κ a, lift_pow p k f hsurj hnil κ a⟩
  have hxy : FrobeniusFixedLifts.fixedMap p (degree p k) f x = FrobeniusFixedLifts.fixedMap p (degree p k) f y :=
    Subtype.ext ((hg a).trans (lift_spec p k f hsurj hnil κ a).symm)
  exact congrArg Subtype.val (FrobeniusFixedLifts.fixedMap_injective p (degree p k) (degree p k).pos f hnil hxy)

theorem lift_natural (κ : k →+* S) (a : R →+* R) (b : S →+* S)
    (h : ∀ r : R, f (a r) = b (f r)) (x : k) :
    a (lift p k f hsurj hnil κ x) = lift p k f hsurj hnil (b.comp κ) x := by
  have he : a.comp (lift p k f hsurj hnil κ) = lift p k f hsurj hnil (b.comp κ) := by
    apply lift_unique
    intro z
    exact (h _).trans (congrArg b (lift_spec p k f hsurj hnil κ z))
  exact DFunLike.congr_fun he x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFieldLift
