import Mathlib

/-! # Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Transfer

noncomputable section

/-!
# IntegralComparison: constructing divided powers through separating ring maps

This construction is used for the divided-power envelope. A family of
ring maps separates elements, and the desired divided powers are explicitly
shown to lie in their common image. The divided-power identities then
follow from the identities in the target rings.
-/

section

universe u v w

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {ι : Type v} {B : ι → Type w} [∀ i, CommRing (B i)]
variable (J : ∀ i, Ideal (B i)) (δ : ∀ i, DividedPowers (J i))
variable (f : ∀ i, A →+* B i)
variable (hinj : ∀ x y : A, (∀ i, f i x = f i y) → x = y)
variable (hI : ∀ i, I ≤ (J i).comap (f i))
variable (hmem : ∀ (n : ℕ) {x : A}, x ∈ I →
  ∃ y : A, (n ≠ 0 → y ∈ I) ∧ ∀ i, f i y = (δ i).dpow n (f i x))

private def operation (n : ℕ) (x : A) : A := by
  classical
  exact if hx : x ∈ I then (hmem n hx).choose else 0

private lemma operation_map (n : ℕ) {x : A} (hx : x ∈ I) (i : ι) :
    f i (operation I J δ f hmem n x) = (δ i).dpow n (f i x) := by
  rw [operation, dite_eq_left hx]
  exact (hmem n hx).choose_spec.2 i

private lemma operation_mem (n : ℕ) (hn : n ≠ 0) {x : A} (hx : x ∈ I) :
    operation I J δ f hmem n x ∈ I := by
  rw [operation, dite_eq_left hx]
  exact (hmem n hx).choose_spec.1 hn

/-- Construct divided powers by verifying them in a separating family of
actual divided-power rings. -/
def dividedPowers : DividedPowers I where
  dpow := operation I J δ f hmem
  dpow_null hx := by rw [operation, dite_eq_right hx]
  dpow_zero hx := by
    apply hinj
    intro i
    rw [operation_map I J δ f hmem _ hx, (δ i).dpow_zero (hI i hx), map_one]
  dpow_one hx := by
    apply hinj
    intro i
    rw [operation_map I J δ f hmem _ hx, (δ i).dpow_one (hI i hx)]
  dpow_mem hn hx := operation_mem I J δ f hmem _ hn hx
  dpow_add hx hy := by
    apply hinj
    intro i
    rw [operation_map I J δ f hmem _ (I.add_mem hx hy), map_add,
      (δ i).dpow_add (hI i hx) (hI i hy), map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_mul, operation_map I J δ f hmem _ hx, operation_map I J δ f hmem _ hy]
  dpow_mul hx := by
    apply hinj
    intro i
    rw [operation_map I J δ f hmem _ (I.mul_mem_left _ hx), map_mul,
      (δ i).dpow_mul (hI i hx), map_mul, map_pow, operation_map I J δ f hmem _ hx]
  mul_dpow hx := by
    apply hinj
    intro i
    rw [map_mul, operation_map I J δ f hmem _ hx, operation_map I J δ f hmem _ hx,
      (δ i).mul_dpow (hI i hx), map_mul, map_natCast, operation_map I J δ f hmem _ hx]
  dpow_comp hn hx := by
    apply hinj
    intro i
    rw [operation_map I J δ f hmem _ (operation_mem I J δ f hmem _ hn hx),
      operation_map I J δ f hmem _ hx, (δ i).dpow_comp hn (hI i hx),
      map_mul, map_natCast, operation_map I J δ f hmem _ hx]

lemma dividedPowers_map (n : ℕ) {x : A} (hx : x ∈ I) (i : ι) :
    f i ((dividedPowers I J δ f hinj hI hmem).dpow n x) = (δ i).dpow n (f i x) :=
  operation_map I J δ f hmem n hx i

end

variable {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}

/-- A ring map killing the divided-power ideal is a morphism to the zero
divided-power ideal. -/
def mapToBot (δ : DividedPowers I) (f : A →+* B) (hf : I ≤ RingHom.ker f) :
    DividedPowers.DPMorphism δ (dividedPowersBot B) where
  toRingHom := f
  ideal_comp := Ideal.map_le_iff_le_comap.mpr hf
  dpow_comp x hx := by
    have hx0 : f x = 0 := hf hx
    rw [hx0]
    rename_i n
    by_cases hn : n = 0
    · subst n
      rw [(dividedPowersBot B).dpow_zero (Ideal.zero_mem _), δ.dpow_zero hx, map_one]
    · rw [(dividedPowersBot B).dpow_eval_zero hn]
      exact (hf (δ.dpow_mem hn hx)).symm

def botMap (f : A →+* B) : DividedPowers.DPMorphism (dividedPowersBot A) (dividedPowersBot B) :=
  mapToBot (dividedPowersBot A) f (by
    intro x hx
    rw [Ideal.mem_bot.mp hx]
    exact map_zero f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Transfer
