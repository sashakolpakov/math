import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicSequenceDifferences

/-! # Compatible Adic Ideals -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompatibleAdicIdeals

noncomputable section

/-! Compatible ideals modulo powers of an ideal come from an actual
ideal in a complete ring. The construction is their intersection. -/

universe u
variable {R : Type u} [CommRing R]
variable (I : Ideal R) [IsPrecomplete I R]
variable (J : ℕ → Ideal R)
variable (hpow : ∀ n, I ^ n ≤ J n)
variable (hstep : ∀ n, J (n + 1) ⊔ I ^ n = J n)

include hstep in
omit [IsPrecomplete I R] in
theorem compatibleAdicIdeals_antitone : Antitone J := by
  apply antitone_nat_of_succ_le
  intro n
  exact le_sup_left.trans_eq (hstep n)

include hpow hstep in
theorem compatibleAdicIdeals_lift (n : ℕ) (x : R) (hx : x ∈ J n) :
    ∃ a : R, a ∈ ⨅ k, J k ∧ x - a ∈ I ^ n := by
  have hs : ∀ k (y : J k), ∃ z : J (k + 1), (y : R) - z ∈ I ^ k := by
    intro k y
    have hy : (y : R) ∈ J (k + 1) ⊔ I ^ k := (hstep k).symm ▸ y.property
    obtain ⟨z, hz, e, he, hze⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨z, hz⟩, ?_⟩
    have hyz : (y : R) - z = e := by rw [← hze]; abel
    simpa only [hyz] using he
  let next (k : ℕ) (y : J k) : J (k + 1) := (hs k y).choose
  have hnext (k : ℕ) (y : J k) : (y : R) - next k y ∈ I ^ k := (hs k y).choose_spec
  let z : (k : ℕ) → J (n + k) :=
    Nat.rec (motive := fun k => J (n + k)) ⟨x, hx⟩ (fun k y => next (n + k) y)
  have hz : ∀ k, (z k).val - (z (k + 1)).val ∈ I ^ (n + k) := by
    intro k
    exact hnext (n + k) (z k)
  obtain ⟨a, ha, hxa⟩ := AdicSequenceDifferences.adic_sequence_limit I n (fun k => (z k).val) hz
  refine ⟨a, ?_, hxa⟩
  rw [Ideal.mem_iInf]
  intro k
  have hzk : (z k).val ∈ J k :=
    compatibleAdicIdeals_antitone I J hstep (Nat.le_add_left k n) (z k).property
  have hdiff : (z k).val - a ∈ J k := hpow k (ha k)
  convert (J k).sub_mem hzk hdiff using 1
  abel

include hpow hstep in
theorem compatibleAdicIdeals_intersection (n : ℕ) :
    (⨅ k, J k) ⊔ I ^ n = J n := by
  apply le_antisymm (sup_le (iInf_le J n) (hpow n))
  intro x hx
  obtain ⟨a, ha, hxa⟩ := compatibleAdicIdeals_lift I J hpow hstep n x hx
  exact Submodule.mem_sup.mpr ⟨a, ha, x - a, hxa, by abel⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompatibleAdicIdeals
