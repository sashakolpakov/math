import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import Mathlib.RingTheory.LocalRing.Length

/-! # Tor Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.TorLength

noncomputable section

/-! Under a flat local extension, every Tor length is multiplied by the
length of the closed fiber. The same holds for the bounded alternating sum
in the geometric intersection coefficient, with its exact ENat.toNat
convention. -/

open _root_.CategoryTheory
open scoped TensorProduct BigOperators

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

theorem tor_length (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.length S (((Tor (ModuleCat S) n).obj ((Extension.baseChange R S).obj M)).obj
      ((Extension.baseChange R S).obj N)) =
      Module.length R (((Tor (ModuleCat R) n).obj M).obj N) *
        Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  rw [(Extension.torBaseChangeIso R S M N n).toLinearEquiv.length_eq]
  exact IsLocalRing.length_baseChange R S _

theorem euler_length (M N : ModuleCat.{u} R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj ((Extension.baseChange R S).obj M)).obj
        ((Extension.baseChange R S).obj N))).toNat) =
      (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        (Module.length R (((Tor (ModuleCat R) i).obj M).obj N)).toNat) *
        (Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))).toNat := by
  simp only [tor_length, ENat.toNat_mul, Nat.cast_mul, ← mul_assoc, Finset.sum_mul]

theorem euler_length_of_maximalIdeal (M N : ModuleCat.{u} R) (d : ℕ)
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj ((Extension.baseChange R S).obj M)).obj
        ((Extension.baseChange R S).obj N))).toNat) =
      (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        (Module.length R (((Tor (ModuleCat R) i).obj M).obj N)).toNat) := by
  rw [euler_length, h]
  have hl : Module.length S (S ⧸ IsLocalRing.maximalIdeal S) = 1 := by
    rw [Module.length_eq_of_surjective (M := S ⧸ IsLocalRing.maximalIdeal S)
      (show Function.Surjective (algebraMap S (S ⧸ IsLocalRing.maximalIdeal S)) from
        Ideal.Quotient.mk_surjective)]
    exact Module.length_eq_one (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S)
  rw [hl]
  norm_num

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.TorLength
