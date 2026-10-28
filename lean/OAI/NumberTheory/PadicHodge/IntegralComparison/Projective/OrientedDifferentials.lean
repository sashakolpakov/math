import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialTransition

/-! # Oriented Differentials -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedDifferentials

noncomputable section

/-! The signed top differential frames have the exact transition of
O(-n-1), over every commutative base ring. -/

open Equiv OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoordinateJacobian OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementSign

universe u v w
variable {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
  {R : Type w} [CommRing R] [Algebra R S] [Module R M]
  {n : ℕ}

def complementIndex (i k : Fin (n + 1)) (h : k ≠ i) : Fin n :=
  (finSuccAboveEquiv i).symm ⟨k, h⟩

@[simp] theorem succAbove_complementIndex (i k : Fin (n + 1)) (h : k ≠ i) :
    i.succAbove (complementIndex i k h) = k :=
  congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨k, h⟩)

theorem coordinates_swap (i k : Fin (n + 1)) (h : k ≠ i) (u : Sˣ)
    (x : Fin (n + 1) → S) (hi : x i = 1) (j : Fin n) :
    CoordinateJacobian.coordinates (complementIndex i k h) u (fun j => x (i.succAbove j)) j =
      ((u⁻¹ : Sˣ) : S) * x (swap i k (i.succAbove j)) := by
  by_cases hj : j = complementIndex i k h
  · subst j
    simp [CoordinateJacobian.coordinates, hi]
  · have hjk : i.succAbove j ≠ k := by
      intro he
      exact hj (i.succAbove_right_injective (he.trans (succAbove_complementIndex i k h).symm))
    rw [CoordinateJacobian.coordinates, ite_eq_right hj, swap_apply_of_ne_of_ne (Fin.succAbove_ne i j) hjk]

theorem signed_wedge_transition (D : Derivation R S M) (i k : Fin (n + 1))
    (h : k ≠ i) (u : Sˣ) (x : Fin (n + 1) → S) (hi : x i = 1) (hk : x k = (u : S)) :
    (((-1 : ℤˣ) ^ k.val * (-1) * (-1) ^ i.val)) •
        exteriorPower.ιMulti S n (fun j => D (((u⁻¹ : Sˣ) : S) * x (k.succAbove j))) =
      (-((u⁻¹ : Sˣ) : S) ^ (n + 1)) •
        exteriorPower.ιMulti S n (fun j => D (x (i.succAbove j))) := by
  have hw := DifferentialTransition.wedge_differential_coordinates D
    (complementIndex i k h) u (fun j => x (i.succAbove j)) (by simpa using hk)
  have he : (fun j => D (CoordinateJacobian.coordinates (complementIndex i k h) u
      (fun j => x (i.succAbove j)) j)) =
      (fun j => D (((u⁻¹ : Sˣ) : S) * x (k.succAbove j))) ∘ ComplementSign.complement (swap i k) i := by
    funext j
    rw [coordinates_swap i k h u x hi]
    simp only [Function.comp_apply]
    congr 2
    apply congrArg x
    simpa only [swap_apply_left] using (ComplementSign.succAbove_complement (swap i k) i j).symm
  rw [he, AlternatingMap.map_perm, ComplementSign.sign_complement_swap i k h.symm] at hw
  exact hw

theorem oriented_wedge_transition (D : Derivation R S M) (i k : Fin (n + 1))
    (h : k ≠ i) (u : Sˣ) (x : Fin (n + 1) → S) (hi : x i = 1) (hk : x k = (u : S)) :
    (-1 : S) ^ i.val • exteriorPower.ιMulti S n (fun j => D (x (i.succAbove j))) =
      (u : S) ^ (n + 1) • ((-1 : S) ^ k.val •
        exteriorPower.ιMulti S n (fun j => D (((u⁻¹ : Sˣ) : S) * x (k.succAbove j)))) := by
  have hw := signed_wedge_transition D i k h u x hi hk
  simp only [Units.smul_def, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, ← Int.cast_smul_eq_zsmul S,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hw
  have hsign : (-1 : S) ^ i.val * (-1 : S) ^ i.val = 1 := by
    rw [← mul_pow]
    simp
  have hu : (u : S) ^ (n + 1) * ((u⁻¹ : Sˣ) : S) ^ (n + 1) = 1 := by
    rw [← mul_pow, Units.mul_inv]
    exact one_pow _
  have he := congrArg (fun z => (-((u : S) ^ (n + 1)) * (-1 : S) ^ i.val) • z) hw
  simp only [smul_smul] at he
  have hl : -((u : S) ^ (n + 1)) * (-1 : S) ^ i.val *
      ((-1 : S) ^ k.val * -1 * (-1 : S) ^ i.val) = (u : S) ^ (n + 1) * (-1 : S) ^ k.val := by
    calc
      _ = (u : S) ^ (n + 1) * (-1 : S) ^ k.val *
          ((-1 : S) ^ i.val * (-1 : S) ^ i.val) := by ring
      _ = _ := by rw [hsign, mul_one]
  have hr : -((u : S) ^ (n + 1)) * (-1 : S) ^ i.val *
      -((u⁻¹ : Sˣ) : S) ^ (n + 1) = (-1 : S) ^ i.val := by
    calc
      _ = ((u : S) ^ (n + 1) * ((u⁻¹ : Sˣ) : S) ^ (n + 1)) * (-1 : S) ^ i.val := by ring
      _ = _ := by rw [hu, one_mul]
  rw [hl, hr] at he
  simpa only [smul_smul] using he.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedDifferentials
