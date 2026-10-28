import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Truncation Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.TruncationTransition

noncomputable section

/-! Canonical compatible maps between the original divided-power truncations. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation

universe u

variable (A : Type u) [CommRing A] (I : Ideal A) (δ : DividedPowers I)
  (n m : ℕ) (hnm : n ≤ m)

def map : AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring A I m →+* AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring A I n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))

theorem map_quotient :
    (map A I n m hnm).comp (Ideal.Quotient.mk (I ^ (m + 1))) = Ideal.Quotient.mk (I ^ (n + 1)) :=
  Ideal.Quotient.factor_comp_mk _

theorem map_isDPMorphism : DividedPowers.IsDPMorphism
    (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ m) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n) (map A I n m hnm) := by
  apply DividedPowers.IsDPMorphism.of_comp δ (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ m) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n)
    (Ideal.Quotient.mk (I ^ (m + 1))) (map A I n m hnm) rfl (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism A I δ m)
  rw [map_quotient]
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism A I δ n

def dpMap : DividedPowers.DPMorphism (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ m) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n) where
  toRingHom := map A I n m hnm
  ideal_comp := (map_isDPMorphism A I δ n m hnm).ideal_comp
  dpow_comp := (map_isDPMorphism A I δ n m hnm).dpow_comp

theorem map_surjective : Function.Surjective (map A I n m hnm) := by
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

theorem map_refl : map A I n n le_rfl = RingHom.id (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring A I n) := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

theorem map_comp (l : ℕ) (hml : m ≤ l) :
    (map A I n m hnm).comp (map A I m l hml) = map A I n l (hnm.trans hml) := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

variable {C : Type u} [CommRing C] (ρ : A →+* C) (hker : RingHom.ker ρ = I)

theorem reduction_map : (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction A I ρ hker n).comp (map A I n m hnm) = AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction A I ρ hker m := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.TruncationTransition
