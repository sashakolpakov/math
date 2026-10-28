import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdRenameProgram

namespace OAI.Algorithms

/-! Polynomial bounds for the actual raw-ID renaming program. -/

namespace SubexponentialSAT.Subexp.RawIdRenameBounds

open BitProgram StructuredCalls RawIdEncoding RawIdRenameProgram

def dictionarySize (dictionary : List Word) : ℕ := (ProgramEncoding.encodeRecords dictionary).length

theorem rank_le_bytes (dictionary : List Word) (query : Word) :
    dictionary.idxOf query ≤ dictionarySize dictionary := by
  have hcount := Encoding.length_encodeList_lower (id : Word → Word) dictionary
  have hr : dictionary.idxOf query ≤ dictionary.length := by
    simpa only [List.idxOf, beq_eq_decide] using
      (List.idxOf_le_length (a := query) (l := dictionary))
  exact hr.trans (by simpa [dictionarySize, ProgramEncoding.encodeRecords] using
    (Nat.le_succ dictionary.length).trans hcount)

theorem code_le_bytes (dictionary : List Word) (l : Literal) :
    codeIn dictionary l ≤ 2 * dictionarySize dictionary + 1 := by
  have hr := rank_le_bytes dictionary l.variable
  unfold codeIn
  cases hp : l.positive <;> simp [] <;> omega

theorem literalBudget_le (dictionary : List Word) (l : Literal) :
    literalBudget dictionary l ≤ 200 * ((literalBytes l).length + dictionarySize dictionary + 1)^2 := by
  have hr := rank_le_bytes dictionary l.variable
  have hc := code_le_bytes dictionary l
  have hid : l.variable.length ≤ (literalBytes l).length := by rw [literalBytes_length]; omega
  have hlookup : SubexpNodeIndexProgram.Internal.budget l.variable dictionary ≤
      (9 * (literalBytes l).length + 80) * (dictionarySize dictionary + 1) := by
    unfold SubexpNodeIndexProgram.Internal.budget dictionarySize
    exact Nat.mul_le_mul_right _ (by omega)
  unfold literalBudget
  nlinarith

theorem clauseResult_le (dictionary : List Word) (C : Clause) :
    (clauseResult dictionary C).length ≤ 1 + (4 * dictionarySize dictionary + 6) * C.length := by
  have h := Encoding.length_encodeList_upper Encoding.encodeNat
    (clauseCodes dictionary C) (2 * dictionarySize dictionary + 2) (by
      intro n hn
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hn)
      rw [Encoding.length_encodeNat]
      exact Nat.add_le_add_right (code_le_bytes dictionary l) 1)
  change (clauseResult dictionary C).length ≤ _ at h
  simp only [clauseCodes, List.length_reverse, List.length_map] at h
  nlinarith

theorem clauseBudget_le_global (dictionary : List Word) (C : Clause) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ l ∈ C, (literalBytes l).length + dictionarySize dictionary + 1 ≤ M) :
    clauseBudget dictionary C ≤ 202 * M^2 * C.length := by
  induction C with
  | nil => simp [clauseBudget]
  | cons l C ih =>
      have hl := (literalBudget_le dictionary l).trans
        (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (h l (by simp)) 2))
      have ht := ih (fun x hx => h x (by simp [hx]))
      have hm2 : 1 ≤ M^2 := Nat.one_le_pow _ _ hM
      simp only [clauseBudget, List.length_cons]
      nlinarith

theorem clauseCost_le_global (dictionary : List Word) (C : Clause) (M : ℕ)
    (hM : dictionarySize dictionary + 1 ≤ M)
    (h : ∀ l ∈ C, (literalBytes l).length + dictionarySize dictionary + 1 ≤ M) :
    clauseCost dictionary C ≤ 9 * (clauseBytes C).length + 29 + 300 * M^2 * C.length := by
  have hm : 1 ≤ M := by omega
  have hmpow : M ≤ M^2 := by
    simpa using Nat.pow_le_pow_right hm (show 1 ≤ 2 by decide)
  have hc := clauseBudget_le_global dictionary C M hm h
  have ho := clauseResult_le dictionary C
  have hcoef : 32 * dictionarySize dictionary + 48 + 202 * M^2 ≤ 300 * M^2 := by
    nlinarith
  have hscaled := Nat.mul_le_mul_right C.length hcoef
  unfold clauseCost
  nlinarith

def sumClauseBytes (F : Formula) : ℕ := (F.map (fun C => (clauseBytes C).length)).sum

theorem sumClauseBytes_le (F : Formula) : sumClauseBytes F ≤ (encode F).length := by
  induction F with
  | nil => simp [sumClauseBytes, encode]
  | cons C F ih =>
      simp only [sumClauseBytes, List.map_cons, List.sum_cons, encode,
        Encoding.length_encodeList_cons] at *
      omega

theorem formulaBudget_le_global (dictionary : List Word) (F : Formula) (M : ℕ)
    (hM : dictionarySize dictionary + 1 ≤ M)
    (h : ∀ C ∈ F, ∀ l ∈ C, (literalBytes l).length + dictionarySize dictionary + 1 ≤ M) :
    formulaBudget dictionary F ≤ 9 * sumClauseBytes F + 31 * F.length +
      300 * M^2 * F.flatten.length := by
  induction F with
  | nil => simp [formulaBudget, sumClauseBytes]
  | cons C F ih =>
      have hc := clauseCost_le_global dictionary C M hM (h C (by simp))
      have ht := ih (fun D hD => h D (by simp [hD]))
      simp only [formulaBudget, sumClauseBytes, List.map_cons, List.sum_cons,
        List.length_cons, List.flatten_cons, List.length_append] at *
      nlinarith

theorem formulaBudget_polynomial (dictionary : List Word) (F : Formula) :
    formulaBudget dictionary F + 5 ≤ 500 * ((encode F).length + dictionarySize dictionary + 1)^3 := by
  let M := (encode F).length + dictionarySize dictionary + 1
  have hM : dictionarySize dictionary + 1 ≤ M := by dsimp [M]; omega
  have hg := formulaBudget_le_global dictionary F M hM (by
    intro C hC l hl
    have h := RawIdRenaming.literal_bytes_le_input F C hC l hl
    dsimp [M]
    omega)
  have hc := sumClauseBytes_le F
  have hf := formula_length_le_bytes F
  have ho := occurrences_le_bytes F
  have hm : 1 ≤ M := by omega
  have hl : (encode F).length ≤ M := by dsimp [M]; omega
  have hmul := Nat.mul_le_mul_left (300 * M^2) (ho.trans hl)
  have hm2 : M ≤ M^2 := by
    simpa using Nat.pow_le_pow_right hm (show 1 ≤ 2 by decide)
  have hm3 : M^2 ≤ M^3 := Nat.pow_le_pow_right hm (by decide)
  have hm13 : 1 ≤ M^3 := hm.trans (hm2.trans hm3)
  change _ ≤ 500 * M^3
  nlinarith

theorem program_polynomial (regs : Fin 8 → Bool) (dictionary : List Word) (F : Formula) :
    ∃ rf, RunsIn program (500 * ((encode F).length + dictionarySize dictionary + 1)^3)
      ((resting regs (ProgramEncoding.encodeRecords dictionary) (encode F) []).withPC (some program.entry))
      ((resting rf (ProgramEncoding.encodeRecords dictionary) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (formulaCodes dictionary F))).withPC none) := by
  obtain ⟨rf, t, ht, he⟩ := program_runsIn regs dictionary F
  exact ⟨rf, t, ht.trans (formulaBudget_polynomial dictionary F), he⟩

theorem renamedBudget_polynomial (F : Formula) :
    formulaBudget (dictionary F) F + 5 ≤ 32000 * ((encode F).length + 1)^6 := by
  have hd := RawIdRenaming.dictionary_bytes_le F
  have hM : (encode F).length + dictionarySize (dictionary F) + 1 ≤
      4 * ((encode F).length + 1)^2 := by
    change (encode F).length + (Encoding.encodeList id (dictionary F)).length + 1 ≤ _
    nlinarith
  calc
    formulaBudget (dictionary F) F + 5
        ≤ 500 * ((encode F).length + dictionarySize (dictionary F) + 1)^3 :=
          formulaBudget_polynomial _ _
    _ ≤ 500 * (4 * ((encode F).length + 1)^2)^3 :=
      Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hM 3)
    _ = 32000 * ((encode F).length + 1)^6 := by ring

theorem renamed_polynomial (regs : Fin 8 → Bool) (F : Formula) :
    ∃ rf, RunsIn program (32000 * ((encode F).length + 1)^6)
      ((resting regs (ProgramEncoding.encodeRecords (dictionary F)) (encode F) []).withPC (some program.entry))
      ((resting rf (ProgramEncoding.encodeRecords (dictionary F)) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (RawIdRenaming.physicalCodes F))).withPC none) := by
  obtain ⟨rf, t, ht, he⟩ := renamed_run regs F
  exact ⟨rf, t, ht.trans (renamedBudget_polynomial F), he⟩

theorem lifted_renamed {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 22 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : State R S) (regs : Fin 8 → Bool) (F : Formula) :
    ∃ t ≤ 32000 * ((encode F).length + 1)^6, ∃ rf,
      Eval (.call (ProgramLinking.liftProgram program register stack)) t
        (embedState register stack frame
          (resting regs (ProgramEncoding.encodeRecords (dictionary F)) (encode F) []))
        (embedState register stack frame
          (resting rf (ProgramEncoding.encodeRecords (dictionary F)) []
            (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (RawIdRenaming.physicalCodes F)))) := by
  obtain ⟨rf, t, ht, he⟩ := renamed_polynomial regs F
  exact ⟨t, ht, rf, eval_call_lifted program register stack frame hregister hstack he⟩

end SubexponentialSAT.Subexp.RawIdRenameBounds

end OAI.Algorithms
