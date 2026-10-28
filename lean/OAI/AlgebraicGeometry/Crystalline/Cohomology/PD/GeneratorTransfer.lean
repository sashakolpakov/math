import Mathlib.RingTheory.DividedPowers.Padic

/-! # Generator Transfer -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.GeneratorTransfer.PDGeneratorTransfer

noncomputable section

/-!
# Constructing divided powers by lifting operations on ideal generators

To descend a divided-power structure along an injective ring map, it
suffices to lift positive divided powers of generators of the source
ideal. The addition and scaling axioms then supply lifts for the ideal.
-/

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B) (δ : DividedPowers J) (f : A →+* B)

private theorem include_zero {x : A} (hx : f x ∈ J)
    (hp : ∀ n : ℕ, n ≠ 0 → ∃ y ∈ I, f y = δ.dpow n (f x)) (n : ℕ) :
    ∃ y : A, (n ≠ 0 → y ∈ I) ∧ f y = δ.dpow n (f x) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, fun h => (h rfl).elim, (map_one f).trans (δ.dpow_zero hx).symm⟩
  · obtain ⟨y, hy, heq⟩ := hp n hn
    exact ⟨y, fun _ => hy, heq⟩

variable (S : Set A)
  (hmap : (Ideal.span S).map f ≤ J)
  (hgen : ∀ s ∈ S, ∀ n : ℕ, n ≠ 0 → ∃ y ∈ Ideal.span S, f y = δ.dpow n (f s))

include hmap hgen in
theorem lift_positive (x : A) (hx : x ∈ Ideal.span S) (n : ℕ) (hn : n ≠ 0) :
    ∃ y ∈ Ideal.span S, f y = δ.dpow n (f x) := by
  induction hx using Submodule.span_induction generalizing n with
  | mem x hx => exact hgen x hx n hn
  | zero => exact ⟨0, (Ideal.span S).zero_mem, by rw [map_zero, δ.dpow_eval_zero hn]⟩
  | smul a x hx ih =>
    obtain ⟨y, hy, heq⟩ := ih n hn
    refine ⟨a ^ n * y, (Ideal.span S).mul_mem_left _ hy, ?_⟩
    change f (a ^ n * y) = δ.dpow n (f (a * x))
    rw [map_mul, map_pow, heq, map_mul, δ.dpow_mul (hmap (Ideal.mem_map_of_mem f hx))]
  | add x y hx hy ihx ihy =>
    classical
    have hfx : f x ∈ J := hmap (Ideal.mem_map_of_mem f hx)
    have hfy : f y ∈ J := hmap (Ideal.mem_map_of_mem f hy)
    choose ux hux hufx using include_zero (Ideal.span S) J δ f hfx ihx
    choose uy huy hufy using include_zero (Ideal.span S) J δ f hfy ihy
    refine ⟨∑ k ∈ Finset.antidiagonal n, ux k.1 * uy k.2, ?_, ?_⟩
    · apply Submodule.sum_mem
      intro k hk
      by_cases hk₁ : k.1 = 0
      · have hk₂ : k.2 ≠ 0 := by
          have hsum := Finset.mem_antidiagonal.mp hk
          intro hz
          exact hn (by simpa only [hk₁, hz, zero_add] using hsum.symm)
        exact (Ideal.span S).mul_mem_left _ (huy _ hk₂)
      · exact (Ideal.span S).mul_mem_right _ (hux _ hk₁)
    · rw [map_sum, map_add, δ.dpow_add hfx hfy]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, hufx, hufy]

include hmap hgen in
theorem lift_all (n : ℕ) {x : A} (hx : x ∈ Ideal.span S) :
    ∃ y : A, ∃ (_ : n ≠ 0 → y ∈ Ideal.span S), f y = δ.dpow n (f x) := by
  obtain ⟨y, hy, heq⟩ := include_zero (Ideal.span S) J δ f (hmap (Ideal.mem_map_of_mem f hx))
    (lift_positive J δ f S hmap hgen x hx) n
  exact ⟨y, hy, heq⟩

/-- Divided powers on a generated ideal, constructed from generator lifts. -/
def dividedPowers (hf : Function.Injective f) (heq : (Ideal.span S).map f = J) :
    DividedPowers (Ideal.span S) :=
  DividedPowers.ofInjective (Ideal.span S) J f hf δ heq
    (lift_all J δ f S heq.le hgen)

theorem map_dpow (hf : Function.Injective f) (heq : (Ideal.span S).map f = J)
    (n : ℕ) {x : A} (hx : x ∈ Ideal.span S) :
    f ((dividedPowers J δ f S hgen hf heq).dpow n x) = δ.dpow n (f x) := by
  classical
  change f (if hx : x ∈ Ideal.span S then (lift_all J δ f S heq.le hgen n hx).choose else 0) = _
  rw [dite_eq_left hx]
  exact (lift_all J δ f S heq.le hgen n hx).choose_spec.choose_spec

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.GeneratorTransfer.PDGeneratorTransfer
