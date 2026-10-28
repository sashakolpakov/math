import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionOuter

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

def unitBudget (B I A : ℕ) : ℕ := 106 * B + 100 * I + 100 * A + 207

theorem emitEntries_address_length (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).address.length = c.address.length + entries.length := by
  induction entries generalizing c with
  | nil => simp [emitEntries]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).address.length = _
    rw [ih]
    simp [emitted, Nat.add_comm, Nat.add_left_comm]

theorem blockBudget_le (i : ℕ) (entries : List Entry) (c : Context) (B I A : ℕ)
    (hB : ∀ e ∈ entries, (entryWord e).length ≤ B)
    (hI : c.block.length ≤ I) (hA : c.address.length + entries.length ≤ A) :
    blockBudget i entries c ≤ entries.length * unitBudget B I A := by
  induction entries generalizing c with
  | nil => simp [blockBudget]
  | cons e es ih =>
    have he := hB e (by simp)
    have hc : c.address.length ≤ A := by simp only [List.length_cons] at hA; omega
    have hs : 6 * (entryWord e).length + callbackBudget (entryWord e) c.block c.address + 7 ≤
        unitBudget B I A := by
      dsimp [callbackBudget, unitBudget]
      omega
    have ht := ih (emitted c e.1 (entryVertex i e))
      (fun x hx => hB x (by simp [hx])) hI
      (by simpa [emitted, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA)
    calc
      blockBudget i (e :: es) c ≤ unitBudget B I A + es.length * unitBudget B I A :=
        Nat.add_le_add hs ht
      _ = (e :: es).length * unitBudget B I A := by simp [Nat.add_mul, Nat.add_comm]

theorem loopBudget_le (entries : List Entry) (n i : ℕ) (c : Context) (B I A : ℕ)
    (hB : ∀ e ∈ entries, (entryWord e).length ≤ B)
    (hI : c.block.length + n ≤ I)
    (hA : c.address.length + n * entries.length ≤ A) :
    loopBudget entries n i c ≤
      1 + n * (7 * c.buckets.length + entries.length * unitBudget B I A + 13) := by
  induction n generalizing i c with
  | zero => simp [loopBudget]
  | succ n ih =>
    have hbc : c.block.length ≤ I := by omega
    have hac : c.address.length + entries.length ≤ A := by
      simp only [Nat.succ_mul] at hA
      omega
    have hb := blockBudget_le i entries c B I A hB hbc hac
    have hi : (advanced i entries c).block.length + n ≤ I := by
      rw [(advanced_static i entries c).1]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hI
    have ha : (advanced i entries c).address.length + n * entries.length ≤ A := by
      change (emitEntries i entries c).address.length + n * entries.length ≤ A
      rw [emitEntries_address_length]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA
    have hr := ih (i + 1) (advanced i entries c) hi ha
    rw [(advanced_static i entries c).2.1] at hr
    let K := 7 * c.buckets.length + entries.length * unitBudget B I A + 13
    have hk : bodyBudget i entries c + 1 ≤ K := by
      dsimp [bodyBudget, K]
      omega
    change loopBudget entries n (i + 1) (advanced i entries c) ≤ 1 + n * K at hr
    change bodyBudget i entries c + loopBudget entries n (i + 1) (advanced i entries c) + 1 ≤
      1 + (n + 1) * K
    calc
      _ ≤ K + (1 + n * K) := by omega
      _ = _ := by ring

/-- A fixed-degree polynomial in the number and maximum size of the buckets,
the block count, and the initial counters bounds the actual extraction trace. -/
theorem bounded_program_trace (entries : List Entry) (n : ℕ) (c : Context) (B : ℕ)
    (hblock : c.block = []) (hremaining : c.remaining = List.replicate n true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, n ≤ e.2.length)
    (hB : ∀ e ∈ entries, (entryWord e).length ≤ B) (regs : Fin 8 → Bool) :
    ∃ steps ≤ 3 + n * (7 * c.buckets.length + entries.length *
        unitBudget B n (c.address.length + n * entries.length) + 13), ∃ rf,
      BitProgram.Trace program steps ((base regs c).withPC (some program.entry))
        ((base rf (advanceMany entries n 0 c)).withPC none) := by
  obtain ⟨steps, hs, rf, ht⟩ := program_trace entries n c hblock hremaining hbuckets hentries regs
  have hb := loopBudget_le entries n 0 c B n (c.address.length + n * entries.length)
    hB (by simp [hblock]) le_rfl
  exact ⟨steps, by omega, rf, ht⟩

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
