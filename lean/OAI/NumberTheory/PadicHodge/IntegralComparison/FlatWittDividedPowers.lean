import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Flat Witt Divided Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers

noncomputable section

/-! Canonical divided powers on (p) in a flat Witt algebra, constructed by rational injection. -/

open scoped TensorProduct

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (A : Type v) [CommRing A] [Algebra (WittVector p k) A]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : A)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

omit [Fintype k] in
include k in
theorem factorial_division (n : ℕ) (x : A) (hx : x ∈ I) :
    ∃ y : A, (n ≠ 0 → y ∈ I) ∧ (n.factorial : A) * y = x ^ n := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨algebraMap W A ((δ).dpow n (p : W)) * z ^ n, ?_, ?_⟩
  · intro hn
    have hm := Ideal.mem_map_of_mem (algebraMap W A)
      ((δ).dpow_mem hn (Ideal.subset_span (Set.mem_singleton (p : W))))
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at hm
    exact (I).mul_mem_right _ hm
  · have hp := congrArg (algebraMap W A)
      ((δ).factorial_mul_dpow_eq_pow (n := n) (Ideal.subset_span (Set.mem_singleton (p : W))))
    simp only [map_mul, map_natCast, map_pow] at hp
    rw [← mul_assoc, hp, ← mul_pow]

abbrev Rational := K ⊗[W] A

instance ratAlgebra : Algebra ℚ (Rational p k A) :=
  ((algebraMap K (Rational p k A)).comp (algebraMap ℚ K)).toAlgebra

def inclusion : A →+* Rational p k A :=
  (Algebra.TensorProduct.includeRight (R := W) (A := K)).toRingHom

variable [Module.Flat (WittVector p k) A]

omit [Fintype k] [CharP k p] in
theorem inclusion_injective : Function.Injective (inclusion p k A) :=
  Module.Flat.tensorProduct_mk_injective W A K

omit [Fintype k] [Module.Flat (WittVector p k) A] in
theorem factorial_unit (n : ℕ) : IsUnit (n.factorial : Rational p k A) := by
  have h : IsUnit (n.factorial : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  simpa only [map_natCast] using h.map (algebraMap K (Rational p k A))

def dividedPowers : DividedPowers I := by
  classical
  refine DividedPowers.ofInjective I (⊤ : Ideal (Rational p k A))
    (inclusion p k A) (inclusion_injective p k A)
    (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (Rational p k A))) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_eq_top]
    have h : IsUnit (p : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    simpa only [map_natCast] using h.map (algebraMap K (Rational p k A))
  · intro n x hx
    obtain ⟨y, hy, he⟩ := factorial_division p k A n x hx
    refine ⟨y, hy, (factorial_unit p k A n).mul_left_cancel ?_⟩
    rw [(DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (Rational p k A))).factorial_mul_dpow_eq_pow
      (show inclusion p k A x ∈ (⊤ : Ideal (Rational p k A)) from trivial)]
    simpa only [map_mul, map_natCast, map_pow] using congrArg (inclusion p k A) he

omit [Fintype k] in
theorem base_isDPMorphism : DividedPowers.IsDPMorphism δ (FlatWittDividedPowers.dividedPowers p k A) (algebraMap W A) := by
  constructor
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro n x hx
    apply inclusion_injective p k A
    apply (factorial_unit p k A n).mul_left_cancel
    have htarget : algebraMap W A x ∈ I := by
      have h := Ideal.mem_map_of_mem (algebraMap W A) hx
      rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
    have hsource := congrArg ((inclusion p k A).comp (algebraMap W A))
      ((δ).factorial_mul_dpow_eq_pow (n := n) hx)
    have hdest := congrArg (inclusion p k A)
      ((FlatWittDividedPowers.dividedPowers p k A).factorial_mul_dpow_eq_pow (n := n) htarget)
    simp only [map_mul, map_natCast, map_pow, RingHom.comp_apply] at hsource hdest
    exact hdest.trans hsource.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers
