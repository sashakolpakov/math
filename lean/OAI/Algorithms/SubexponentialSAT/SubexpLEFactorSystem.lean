import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BooleanPackingLE
import OAI.Algorithms.SubexponentialSAT.PackedSAT

namespace OAI.Algorithms

/-!
# The factor system matching little-endian materialized chunks

Only the local chunk embedding changes. Chunk scopes, occurrence bounds,
and the exact number of satisfying assignments are preserved. Clause tables
include local-label validity, including the shorter final chunk.
-/

namespace SubexponentialSAT.SubexpLEFactorSystem

noncomputable section

variable {V J : Type*} [DecidableEq V] [DecidableEq J]
variable {b : J → ℕ} {p : ℕ} [NeZero p]

omit [DecidableEq V] in
/-- The actual label convention used by the bit materializer. -/
noncomputable def system (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.System J (J ⊕ {C // C ∈ F}) (ZMod p) :=
  FactorReduction.cnfFactorSystem positions
    (fun j => BooleanPackingLE.chunkZModEmbedding (capacity j)) F

omit [DecidableEq V] in
@[simp] theorem system_scope (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    (system positions capacity F).scope = (FactorReduction.primeLabelCNF positions capacity F).scope := rfl

theorem system_count [Fintype V] [Fintype J]
    (positions : V ≃ (j : J) × Fin (b j)) (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.count (system positions capacity F) = SAT.count F :=
  FactorReduction.cnfFactorSystem_count positions
    (fun j => BooleanPackingLE.chunkZModEmbedding (capacity j)) F

omit [DecidableEq V] in
theorem unary_iff (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) (x : J → ZMod p) (j : J) :
    Factor.evalFactor (system positions capacity F) (.inl j) x = true ↔
      (x j).val < 2 ^ b j := by
  change decide (∃ y, BooleanPackingLE.chunkZModEmbedding (capacity j) y = x j) = true ↔ _
  rw [decide_eq_true_eq]
  exact BooleanPackingLE.mem_range_chunkZModEmbedding (capacity j) (x j)

/- Clause truth alone is insufficient: the local labels must decode to
actual chunks, with their declared (possibly short) widths. -/
omit [DecidableEq V] in
theorem clause_table_iff (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) (e : {C // C ∈ F})
    (x : {j // j ∈ FactorReduction.cnfScope positions F e} → ZMod p) :
    (system positions capacity F).table (.inr e) x = true ↔
      (∀ j, (x j).val < 2 ^ b j.val) ∧
      FactorReduction.cnfTable positions F e
        (fun j => BooleanPackingLE.decodeZMod (b j.val) (x j)) = true := by
  simp only [system, FactorReduction.cnfFactorSystem, FactorReduction.factorSystem,
    FactorReduction.factorTable, decide_eq_true_eq]
  constructor
  · rintro ⟨vals, htable, hvals⟩
    refine ⟨?_, ?_⟩
    · intro j
      exact (BooleanPackingLE.mem_range_chunkZModEmbedding (capacity j.val) (x j)).mp
        ⟨vals j, hvals j⟩
    · have hd : (fun j => BooleanPackingLE.decodeZMod (b j.val) (x j)) = vals := by
        funext j
        rw [← hvals j, BooleanPackingLE.decodeZMod_encode]
      simpa only [hd] using htable
  · rintro ⟨hvalid, htable⟩
    refine ⟨fun j => BooleanPackingLE.decodeZMod (b j.val) (x j), htable, ?_⟩
    intro j
    exact BooleanPackingLE.encode_decodeZMod (capacity j.val) (x j) (hvalid j)

theorem system_bounded [Fintype V] [Fintype J]
    (positions : V ≃ (j : J) × Fin (b j)) (capacity : ∀ j, 2 ^ b j ≤ p)
    (F : SAT.CNF V) (k ell B : ℕ) (hk : 1 ≤ k) (hwidth : SAT.WidthAtMost k F)
    (hocc : SAT.OccurrenceAtMost B F) (hsize : ∀ j, b j ≤ ell)
    (hne : ∀ C ∈ F, C.Nonempty) :
    (system positions capacity F).toPattern.Bounded k (1 + ell * B) :=
  PackedSAT.cnfFactorSystem_bounded positions
    (fun j => BooleanPackingLE.chunkZModEmbedding (capacity j)) F k ell B hk hwidth hocc hsize hne

section Canonical

variable {n ell k B : ℕ} [Fact p.Prime]

noncomputable def packed (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n)) :=
  system (ChunkPartition.indexEquiv n ell hell) (PackedSAT.capacity (n := n) hcap) F

omit [Fact (Nat.Prime p)] in
theorem packed_count (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n)) :
    Factor.count (packed hell hcap F) = SAT.count F :=
  system_count _ _ _

omit [Fact (Nat.Prime p)] in
theorem packed_bounded (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (F : SAT.CNF (Fin n))
    (hk : 1 ≤ k) (hwidth : SAT.WidthAtMost k F) (hocc : SAT.OccurrenceAtMost B F)
    (hne : ∀ C ∈ F, C.Nonempty) :
    (packed hell hcap F).toPattern.Bounded k (1 + ell * B) :=
  system_bounded _ _ F k ell B hk hwidth hocc (ChunkPartition.size_le n ell) hne

end Canonical

end

end SubexponentialSAT.SubexpLEFactorSystem

end OAI.Algorithms
