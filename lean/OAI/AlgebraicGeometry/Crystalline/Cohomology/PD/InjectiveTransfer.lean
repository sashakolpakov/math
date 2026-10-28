import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.GeneratorTransfer

/-! # Injective Transfer -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InjectiveTransfer.PDInjectiveTransfer

noncomputable section

/-!
# Divided-power transfer into a larger target ideal

Lifting the target operations along an injective ring map only requires
the source ideal to map into the target ideal. Equality of the two ideals
is unnecessary. This also handles augmentation ideals whose image in a
rational polynomial ring is proper.
-/

variable {A B : Type*} [CommSemiring A] [CommSemiring B]
  (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : Function.Injective f)
  (δ : DividedPowers J) (hIJ : I.map f ≤ J)
  (hmem : ∀ (n : ℕ) {x : A}, x ∈ I →
    ∃ (y : A) (_ : n ≠ 0 → y ∈ I), f y = δ.dpow n (f x))

/-- Transfer along an injection, assuming only inclusion of the image ideal. -/
def dividedPowers : DividedPowers I where
  dpow n x := open scoped Classical in if hx : x ∈ I then (hmem n hx).choose else 0
  dpow_null hx := by simp [dite_eq_right hx]
  dpow_zero {x} hx := by
    simp only [dite_eq_left hx, ← hf.eq_iff, (hmem 0 hx).choose_spec.2, map_one]
    exact δ.dpow_zero (hIJ (Ideal.mem_map_of_mem f hx))
  dpow_one hx := by
    simpa only [dite_eq_left hx, ← hf.eq_iff, (Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2]
      using δ.dpow_one (hIJ (Ideal.mem_map_of_mem f hx))
  dpow_mem {n x} hn hx := by
    simpa only [dite_eq_left hx] using (hmem n hx).choose_spec.1 hn
  dpow_add {n x y} hx hy := by
    have hxy : x + y ∈ I := I.add_mem hx hy
    simpa only [dite_eq_left hxy, dite_eq_left hx, dite_eq_left hy, ← hf.eq_iff, map_sum, map_mul,
      (Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2, map_add]
      using δ.dpow_add (hIJ (I.mem_map_of_mem f hx)) (hIJ (I.mem_map_of_mem f hy))
  dpow_mul {n a x} hx := by
    have hax : a * x ∈ I := I.mul_mem_left _ hx
    simpa only [(Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2, dite_eq_left hax, dite_eq_left hx,
      ← hf.eq_iff, map_mul, map_pow] using δ.dpow_mul (hIJ (I.mem_map_of_mem f hx))
  mul_dpow hx := by
    simpa only [dite_eq_left hx, ← hf.eq_iff, (hmem _ hx).choose_spec.2, map_mul, map_natCast]
      using δ.mul_dpow (hIJ (I.mem_map_of_mem f hx))
  dpow_comp {n m x} hm hx := by
    simp only [dite_eq_left hx, ← hf.eq_iff, map_mul, map_natCast]
    rw [dite_eq_left]
    · simp only [(Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2]
      exact δ.dpow_comp hm (hIJ (I.mem_map_of_mem f hx))
    · rw [dite_eq_left hx]
      exact (hmem m hx).choose_spec.1 hm

theorem map_dpow (n : ℕ) {x : A} (hx : x ∈ I) :
    f ((dividedPowers I J f hf δ hIJ hmem).dpow n x) = δ.dpow n (f x) := by
  classical
  change f (if hx : x ∈ I then (hmem n hx).choose else 0) = _
  rw [dite_eq_left hx]
  exact (hmem n hx).choose_spec.2

variable {A B : Type*} [CommRing A] [CommRing B]
  (J : Ideal B) (δ : DividedPowers J) (f : A →+* B) (S : Set A)
  (hmap : (Ideal.span S).map f ≤ J)
  (hgen : ∀ s ∈ S, ∀ n : ℕ, n ≠ 0 →
    ∃ y ∈ Ideal.span S, f y = δ.dpow n (f s))
  (hf : Function.Injective f)

def fromGenerators : DividedPowers (Ideal.span S) :=
  dividedPowers (Ideal.span S) J f hf δ hmap
    (GeneratorTransfer.PDGeneratorTransfer.lift_all J δ f S hmap hgen)

theorem fromGenerators_map_dpow (n : ℕ) {x : A} (hx : x ∈ Ideal.span S) :
    f ((fromGenerators J δ f S hmap hgen hf).dpow n x) = δ.dpow n (f x) :=
  map_dpow (Ideal.span S) J f hf δ hmap
    (GeneratorTransfer.PDGeneratorTransfer.lift_all J δ f S hmap hgen) n hx

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InjectiveTransfer.PDInjectiveTransfer
