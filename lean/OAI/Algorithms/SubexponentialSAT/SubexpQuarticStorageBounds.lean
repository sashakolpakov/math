import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCandidateContract

namespace OAI.Algorithms

/-! # Bounds on the physical tables left by quartic selection -/

namespace SubexponentialSAT.SubexpQuarticStorageBounds

open BitProgram StructuredCalls SubexpLiftRing SubexpEnumerationPayload SubexpTupleRefinement
open SubexpQuarticProducerControl SubexpQuarticCallback SubexpQuarticScanInvariant
open SubexpQuarticDivisorContracts SubexpQuarticCandidateContract

def linearSize (p : ℕ) : ℕ := 1 + (2 * baseWidth p 1 + 2) * p
def quadraticSize (p : ℕ) : ℕ := 1 + (4 * baseWidth p 1 + 2) * p^2
def candidateSize (p : ℕ) : ℕ := 1 + (8 * baseWidth p 1 + 2) * p^4
def workspaceWidth (p : ℕ) : ℕ :=
  baseWidth p 1 + 1 + linearSize p + quadraticSize p + candidateSize p

theorem linear_size (p : ℕ) [Fact p.Prime] :
    (ProgramEncoding.encodeRecords (linearRecords p)).length ≤ linearSize p := by
  have h := ProgramEncoding.encodeRecords_length_le (linearRecords p) (scalarWidth p) (by
    intro bits hbits
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
    exact ((scalarCode p).length_block a).le)
  simpa [linearRecords, linearSize, baseWidth, scalarWidth] using h

theorem quadratic_size (p : ℕ) [Fact p.Prime] :
    (ProgramEncoding.encodeRecords (quadraticRecords p)).length ≤ quadraticSize p := by
  have h := ProgramEncoding.encodeRecords_length_le (quadraticRecords p) (2 * scalarWidth p) (by
    intro bits hbits
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
    exact (SubexpEnumerationPayload.vectorBits_length (D := 2) a).le)
  simpa [quadraticRecords, quadraticSize, QuarticSearch.length_vectors,
    baseWidth, scalarWidth, ← Nat.mul_assoc] using h

theorem candidate_size (p : ℕ) [Fact p.Prime] :
    (ProgramEncoding.encodeRecords (SubexpQuarticSelector.candidateRecords p)).length ≤
      candidateSize p := by
  have h := ProgramEncoding.encodeRecords_length_le (SubexpQuarticSelector.candidateRecords p)
    (4 * scalarWidth p) (fun bits hbits => (SubexpQuarticSelector.candidateRecord_width p bits hbits).le)
  simpa [candidateSize, baseWidth, scalarWidth, ← Nat.mul_assoc] using h

theorem unread_length (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (ProgramEncoding.encodeRecords records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread, ProgramEncoding.encodeRecords, Encoding.encodeList]
  | cons bits records ih =>
      have hlen : (ProgramEncoding.encodeRecords (bits :: records)).length =
          2 * bits.length + 2 + (ProgramEncoding.encodeRecords records).length :=
        Encoding.length_encodeList_cons id bits records
      rw [hlen]
      simp only [RecordPrograms.unread]
      split
      · simp only [List.append_nil]
        change (ProgramEncoding.encodeRecords records).length ≤ _
        omega
      · omega

theorem final_workspace (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (d : Data) (hd : SearchReady p M d)
    (h28 : d.stacks 28 = RecordPrograms.unread (SubexpQuarticByteSpec.candidateTest p)
      (SubexpQuarticSelector.candidateRecords p) []) (h29 : d.stacks 29 = []) :
    ∀ j : Fin 35, j ≠ 33 → (d.stacks j).length ≤ workspaceWidth p := by
  obtain ⟨⟨c, bank, hrep, _, _, h30, h32, h31⟩, h25, h26, h23, h24, h27, _, h34⟩ := hd
  have hb : baseWidth p 1 + 1 ≤ workspaceWidth p := by unfold workspaceWidth; omega
  have hl : linearSize p ≤ workspaceWidth p := by unfold workspaceWidth; omega
  have hq : quadraticSize p ≤ workspaceWidth p := by unfold workspaceWidth; omega
  have hc : candidateSize p ≤ workspaceWidth p := by unfold workspaceWidth; omega
  intro j hj33
  by_cases hj14 : j.val < 14
  · let i : Fin 14 := ⟨j.val, hj14⟩
    have he : j = bankPort i := Fin.ext rfl
    rw [he, hrep.1]
    exact (bank i).property.le.trans (by omega)
  by_cases hj22 : j.val < 22
  · let i : Fin 8 := ⟨j.val - 14, by omega⟩
    have he : j = workPort i := by apply Fin.ext; change j.val = 14 + (j.val - 14); omega
    rw [he, hrep.2.1]
    have hm : M.bits.length ≤ workspaceWidth p := M.length_le.trans hb
    have hwork (k : Fin 8) :
        (SubexpQuarticMachine.scalarWork [] [] M.bits k).length ≤ workspaceWidth p := by
      fin_cases k <;> simp only [SubexpQuarticMachine.scalarWork]
      all_goals first | exact hm | exact Nat.zero_le _
    exact hwork i
  have hcases : j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨
      j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 34 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hrep.2.2]; exact Nat.zero_le _
  · rw [h23]; exact Nat.zero_le _
  · rw [h24]; exact Nat.zero_le _
  · rw [h25]; exact (linear_size p).trans hl
  · rw [h26]; exact (quadratic_size p).trans hq
  · rw [h27]; exact Nat.zero_le _
  · rw [h28]
    exact ((unread_length _ _).trans (candidate_size p)).trans hc
  · rw [h29]; exact Nat.zero_le _
  · rw [h30]; exact Nat.zero_le _
  · rw [h31]; omega
  · rw [h32]; exact Nat.zero_le _
  · exact h34.trans (by omega)

end SubexponentialSAT.SubexpQuarticStorageBounds

end OAI.Algorithms
