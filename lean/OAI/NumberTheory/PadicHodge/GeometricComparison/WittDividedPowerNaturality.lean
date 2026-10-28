import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers

/-! # Witt Divided Power Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WittDividedPowerNaturality.FlatWittDividedPowerNaturality

noncomputable section

/-! Ring maps between flat Witt algebras preserve the canonical divided powers
on their prime ideals. -/

universe u v w
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (A : Type v) [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  (B : Type w) [CommRing B] [Algebra (WittVector p k) B] [Module.Flat (WittVector p k) B]
  (f : A →+* B)

theorem isDPMorphism : DividedPowers.IsDPMorphism
    (IntegralComparison.FlatWittDividedPowers.dividedPowers p k A)
    (IntegralComparison.FlatWittDividedPowers.dividedPowers p k B) f := by
  constructor
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro n x hx
    apply IntegralComparison.FlatWittDividedPowers.inclusion_injective p k B
    apply (IntegralComparison.FlatWittDividedPowers.factorial_unit p k B n).mul_left_cancel
    have htarget : f x ∈ Ideal.span {(p : B)} := by
      have h := Ideal.mem_map_of_mem f hx
      rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
    have hsource := congrArg ((IntegralComparison.FlatWittDividedPowers.inclusion p k B).comp f)
      ((IntegralComparison.FlatWittDividedPowers.dividedPowers p k A).factorial_mul_dpow_eq_pow (n := n) hx)
    have hdest := congrArg (IntegralComparison.FlatWittDividedPowers.inclusion p k B)
      ((IntegralComparison.FlatWittDividedPowers.dividedPowers p k B).factorial_mul_dpow_eq_pow (n := n) htarget)
    simp only [map_mul, map_natCast, map_pow, RingHom.comp_apply] at hsource hdest
    exact hdest.trans hsource.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WittDividedPowerNaturality.FlatWittDividedPowerNaturality
