import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPolynomial

/-! Fixed polynomial bounds from the actual six frontend source words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog in
/-- Physical query words, including arbitrary padding and the actual raw trial
rows, bound the capacity used by the native frontend. This is the same six
port calculation as the original query-width lemma, without its final-resource
constructor import. -/
theorem query_capacity_of_sources (q : LeafQueryFrontend.Query) (k W : ℕ)
    (a : LeafQueryFrontend.Data) (hr : q.Ready a)
    (hw : ∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
      (a.stacks i).length ≤ W) :
    LeafScopeInputBounds.capacity q k ≤
      6 * W + BinaryArithmetic.toNat q.ambient + k + 8 := by
  have h0 := hw 700 (by decide)
  have h1 := hw 701 (by decide)
  have h2 := hw 705 (by decide)
  have h3 := hw 707 (by decide)
  have h4 := hw 708 (by decide)
  have h5 := hw 709 (by decide)
  rw [hr.1] at h0
  rw [hr.2.1] at h1
  rw [hr.2.2.1] at h2
  rw [hr.2.2.2.2.1] at h3
  rw [hr.2.2.2.2.2.1] at h4
  rw [hr.2.2.2.2.2.2.1] at h5
  unfold LeafScopeInputBounds.capacity
  omega

open SqrtLog in
/-- Uniform physical word bounds imply the six source bounds. -/
theorem query_capacity_of_words (q : LeafQueryFrontend.Query) (k W : ℕ)
    (a : LeafQueryFrontend.Data) (hr : q.Ready a)
    (hw : ∀ i, (a.stacks i).length ≤ W) :
    LeafScopeInputBounds.capacity q k ≤
      6 * W + BinaryArithmetic.toNat q.ambient + k + 8 :=
  query_capacity_of_sources q k W a hr (fun i _ => hw i)

open SqrtLog in
/-- The complete native frontend has a fixed polynomial in the actual query
word cap and ambient size. Numeric correctness alone is not used to bound
padding, raw rows, or any other retained word. -/
theorem query_frontend_sources_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (k W : ℕ)
      (a : LeafQueryFrontend.Data), q.Valid → q.Ready a →
      (∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
        (a.stacks i).length ≤ W) →
      q.inputBudget k ≤ C * (W + BinaryArithmetic.toNat q.ambient + k + 1) ^ degree := by
  obtain ⟨C, degree, hfront⟩ := LeafQueryFrontend.inputBudget_polynomial
  refine ⟨C * 9 ^ degree, degree, ?_⟩
  intro q k W a hvalid hready hwords
  have hcap := query_capacity_of_sources q k W a hready hwords
  have hsize : LeafScopeInputBounds.capacity q k + 1 ≤
      9 * (W + BinaryArithmetic.toNat q.ambient + k + 1) := by omega
  calc
    _ ≤ C * (9 * (W + BinaryArithmetic.toNat q.ambient + k + 1)) ^ degree :=
      (hfront q k hvalid).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree))
    _ = _ := by rw [mul_pow]; ring

open SqrtLog in
/-- The all-word version remains available to source-space callers. -/
theorem query_frontend_physical_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (k W : ℕ)
      (a : LeafQueryFrontend.Data), q.Valid → q.Ready a →
      (∀ i, (a.stacks i).length ≤ W) →
      q.inputBudget k ≤ C * (W + BinaryArithmetic.toNat q.ambient + k + 1) ^ degree := by
  obtain ⟨C, degree, h⟩ := query_frontend_sources_polynomial
  exact ⟨C, degree, fun q k W a hv hr hw => h q k W a hv hr (fun i _ => hw i)⟩



open SqrtLog in
/-- The concrete cubic source cap supplied by the staged hash query remains a
fixed polynomial through the complete physical frontend. The constants precede
all actual queries, marks, source padding and caller states. -/
theorem query_frontend_cubic_sources_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (k S : ℕ)
      (a : LeafQueryFrontend.Data), q.Valid → q.Ready a →
      BinaryArithmetic.toNat q.ambient ≤ S → k ≤ S →
      (∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
        (a.stacks i).length ≤ 16 * S ^ 3) →
      q.inputBudget k ≤ C * (S + 1) ^ degree := by
  obtain ⟨C, degree, h⟩ := query_frontend_sources_polynomial
  refine ⟨C * 19 ^ degree, 3 * degree, ?_⟩
  intro q k S a hv hr hn hk hw
  have hS : S ≤ (S + 1) ^ 3 := (Nat.le_succ S).trans (by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1 ≤ S + 1 by omega) (show 1 ≤ 3 by decide)))
  have h0 : 1 ≤ (S + 1) ^ 3 := Nat.one_le_pow' _ S
  have hp : S ^ 3 ≤ (S + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ S) 3
  have hb : 16 * S ^ 3 + BinaryArithmetic.toNat q.ambient + k + 1 ≤
      19 * (S + 1) ^ 3 := by omega
  calc
    _ ≤ C * (19 * (S + 1) ^ 3) ^ degree :=
      (h q k (16 * S ^ 3) a hv hr hw).trans
        (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb degree))
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
