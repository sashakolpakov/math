import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.Order
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Factor Extraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorExtraction.Construction

noncomputable section

/-! Finite extraction of boundary powers from a nonzero local ideal. -/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Extract the largest power of one proper principal boundary ideal.
The residual ideal grows, stays nonzero, and is no longer divisible by that equation. -/
theorem exists_boundary_power_factor (J : Ideal R) (hJ : J ≠ ⊥) (z : R)
    (hz : Ideal.span {z} ≠ ⊤) :
    ∃ (e : ℕ) (L : Ideal R), J = Ideal.span {z ^ e} * L ∧
      J ≤ L ∧ L ≠ ⊥ ∧ ¬ L ≤ Ideal.span {z} := by
  obtain ⟨e, he, he1⟩ := Blowups.Ideal.Order.Construction.exists_idealAdicOrder (Ideal.span {z}) J hz hJ
  let L := J.colon (Ideal.span {z ^ e})
  have hfactor : J = Ideal.span {z ^ e} * L :=
    (ControlledTransform.Construction.principal_mul_colon_of_le J (z ^ e) (by simpa only [Ideal.span_singleton_pow] using he)).symm
  have hJL : J ≤ L := by
    rw [hfactor]
    exact Ideal.mul_le_right
  refine ⟨e, L, hfactor, hJL, ?_, ?_⟩
  · intro hL
    exact hJ (bot_unique (hL ▸ hJL))
  · intro hL
    apply he1
    calc
      J = Ideal.span {z ^ e} * L := hfactor
      _ ≤ Ideal.span {z ^ e} * Ideal.span {z} := Ideal.mul_mono le_rfl hL
      _ = Ideal.span {z} ^ (e + 1) := by rw [pow_succ, Ideal.span_singleton_pow]

variable {ι : Type*} [DecidableEq ι]

/-- A finite family of proper boundary equations can be factored from an
arbitrary nonzero local ideal. The remaining ideal is divisible by none of
those equations. No canonical ordering or uniqueness assertion is required. -/
theorem exists_finite_boundary_factorization (s : Finset ι) (z : ι → R)
    (hz : ∀ i ∈ s, Ideal.span {z i} ≠ ⊤) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ (a : ι → ℕ) (L : Ideal R),
      (∀ i ∉ s, a i = 0) ∧ J = Ideal.span {∏ i ∈ s, z i ^ a i} * L ∧
        J ≤ L ∧ L ≠ ⊥ ∧ ∀ i ∈ s, ¬ L ≤ Ideal.span {z i} := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty =>
    refine ⟨fun _ => 0, J, ?_, ?_, le_rfl, hJ, ?_⟩
    · intro i _
      rfl
    · rw [Finset.prod_empty, Ideal.span_singleton_one, Ideal.top_mul]
    · intro i hi
      exact False.elim (Finset.notMem_empty i hi)
  | @insert i s his ih =>
    obtain ⟨e, U, hJU, hJleU, hU, hUi⟩ := exists_boundary_power_factor J hJ (z i)
      (hz i (Finset.mem_insert_self i s))
    obtain ⟨a, L, ha, hUL, hUleL, hL, hLs⟩ := ih
      (fun j hj => hz j (Finset.mem_insert_of_mem hj)) U hU
    refine ⟨Function.update a i e, L, ?_, ?_, hJleU.trans hUleL, hL, ?_⟩
    · intro j hj
      have hji : j ≠ i := by
        intro heq
        subst j
        exact hj (Finset.mem_insert_self i s)
      rw [Function.update_of_ne hji]
      exact ha j (fun hjs => hj (Finset.mem_insert_of_mem hjs))
    · have hprod : (∏ j ∈ s, z j ^ Function.update a i e j) = ∏ j ∈ s, z j ^ a j := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (by
          intro hji
          subst j
          exact his hj)]
      rw [Finset.prod_insert his, Function.update_self, hprod,
        hJU, hUL, ← mul_assoc, Ideal.span_singleton_mul_span_singleton]
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact fun h => hUi (hUleL.trans h)
      · exact hLs j hjs

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorExtraction.Construction
