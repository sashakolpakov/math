import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutConstruction

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

abbrev Word := List Bool

def clauseBytesBound (S : ℕ) := 1 + (4 * S + 2) * S
def scopeBytesBound (S : ℕ) := 1 + (2 * S + 2) * S
def mappedScopeBytesBound (S : ℕ) := 1 + (2 * (S + 1) + 2) * S
def literalBound (S : ℕ) := SubexpLiteralChunkProgram.budget S S
def scopeCallbackBound (S : ℕ) := literalBound S + 5 * (S + 1) + 14
def scopeProgramBound (S : ℕ) :=
  5 + S * (12 * S + scopeCallbackBound S + 7) +
    10 * mappedScopeBytesBound S + 120 * (mappedScopeBytesBound S + 1) ^ 2
def countScopeBound (S : ℕ) :=
  7 * scopeBytesBound S + 5 + (4 * (S * S) + 6 * S + 5) +
    SubexpFactorCountSetup.budget S S + 1
def candidateBound (S : ℕ) :=
  18 * S + 4 * (S * S) + 7 * clauseBytesBound S + S * (45 * S + 63) + 57
def fieldCallbackBound (S : ℕ) :=
  (S * (100 * (S + S + 1) ^ 2 + 14 * S + 8 * S + 19) + 6 +
    9 * S + 7 * S + 13 + 1) + (14 * (S * S) + 17) +
  (7 * S + 7 * S + 7 * scopeBytesBound S + 15) + 10 +
  (S * (S * (14 * S + 19) + 36 * S + 18 * S + 78) + 3) +
  (2 * S + 2 * S + 7 * S + 19) + (candidateBound S + 1) + 6
def fuelWidthBound (S : ℕ) := 1 + S * S
def enumerationBound (S : ℕ) :=
  8 * fuelWidthBound S + 8 +
    (S * (fieldCallbackBound S + 8 * S + 16 * fuelWidthBound S + 24) + 1)
def unitBound (S : ℕ) :=
  11 + (7 * clauseBytesBound S + 5) + (scopeProgramBound S + 1) +
    (countScopeBound S + 1) + (2 * S + 3) + enumerationBound S +
    (2 * S + 2 * fuelWidthBound S + 2 * S + 20)
def callbackBound (S : ℕ) :=
  unitBound S + 5 * clauseBytesBound S + 8 * S + 8 * scopeBytesBound S + 39

theorem sum_lengths_le (words : List Word) (S : ℕ)
    (h : ∀ w ∈ words, w.length ≤ S) :
    (words.map List.length).sum ≤ words.length * S := by
  induction words with
  | nil => simp
  | cons w words ih =>
      have hw := h w (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem records_budget_le (cost : Word → ℕ) (words : List Word) (S C : ℕ)
    (hsize : ∀ w ∈ words, w.length ≤ S) (hcost : ∀ w ∈ words, cost w ≤ C) :
    RecordPrograms.budget cost words ≤ words.length * (6 * S + C + 7) := by
  induction words with
  | nil => simp [RecordPrograms.budget]
  | cons w words ih =>
      have hw := hsize w (by simp)
      have hc := hcost w (by simp)
      have ht := ih (fun x hx => hsize x (by simp [hx]))
        (fun x hx => hcost x (by simp [hx]))
      simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem clause_bytes_le {n : ℕ} (ls : List (SAT.Literal (Fin n))) (S : ℕ)
    (hn : n ≤ S) (hlen : ls.length ≤ S) :
    (SubexpClauseRowProgram.clauseBytes ls).length ≤ clauseBytesBound S := by
  have h := Encoding.length_encodeList_upper Encoding.encodeNat
    (ls.map Encoding.literalCode) (2 * S) (by
      intro code hc
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
      rw [Encoding.length_encodeNat]
      have := Encoding.literalCode_lt l
      omega)
  simp only [List.length_map] at h
  rw [show 2 * (2 * S) = 4 * S by omega] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) 1)

theorem row_cost_le {n : ℕ} (ls : List (SAT.Literal (Fin n))) (S : ℕ) (hn : n ≤ S) :
    SubexpClauseRowProgram.rowCost ls ≤ ls.length * (45 * S + 63) := by
  induction ls with
  | nil => simp [SubexpClauseRowProgram.rowCost]
  | cons l ls ih =>
      have hv : l.variable.val ≤ S := (Nat.le_of_lt l.variable.isLt).trans hn
      have hb : (if l.positive then 1 else 0) ≤ (1 : ℕ) := by split_ifs <;> decide
      simp only [SubexpClauseRowProgram.rowCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem literal_budget_le (width index S : ℕ) (hw : width ≤ S) (hi : index ≤ S) :
    SubexpLiteralChunkProgram.budget width index ≤ literalBound S := by
  unfold literalBound SubexpLiteralChunkProgram.budget
  gcongr

theorem scope_program_le {n : ℕ} (ell : Word) (ls : List (SAT.Literal (Fin n)))
    (S : ℕ) (he : ell.length ≤ S) (hn : n ≤ S) (hlen : ls.length ≤ S) :
    SubexpScopeProducer.budget ell (SubexpClauseFactorProgram.codes ls) ≤ scopeProgramBound S := by
  let codes := SubexpClauseFactorProgram.codes ls
  have hcodes : codes.length ≤ S := by simpa [codes, SubexpClauseFactorProgram.codes] using hlen
  have hindex : ∀ code ∈ codes, code / 2 ≤ S := by
    intro code hc
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
    have := Encoding.literalCode_lt l
    omega
  have hchunk : ∀ code ∈ codes, SubexpChunkRecordMap.chunk ell code ≤ S := by
    intro code hc
    exact (Nat.div_le_self _ _).trans (hindex code hc)
  have hrecord : ∀ w ∈ codes.map Encoding.encodeNat, w.length ≤ 2 * S := by
    intro w hw
    obtain ⟨code, hc, rfl⟩ := List.mem_map.mp hw
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
    rw [Encoding.length_encodeNat]
    have := Encoding.literalCode_lt l
    omega
  have hcallback : ∀ w ∈ codes.map Encoding.encodeNat,
      SubexpChunkRecordMap.callbackCost ell w ≤ scopeCallbackBound S := by
    intro w hw
    obtain ⟨code, hc, rfl⟩ := List.mem_map.mp hw
    have hb := literal_budget_le ell.length (code / 2) S he (hindex code hc)
    have hm : (Encoding.encodeNat (SubexpChunkRecordMap.chunk ell code)).length ≤ S + 1 := by
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right (hchunk code hc) 1
    simp only [Encoding.length_encodeNat] at hm
    simp only [SubexpChunkRecordMap.callbackCost, Encoding.length_encodeNat,
      Nat.add_sub_cancel, SubexpChunkRecordMap.mappedBits_encodeNat]
    unfold scopeCallbackBound
    omega
  have hr := records_budget_le (SubexpChunkRecordMap.callbackCost ell)
    (codes.map Encoding.encodeNat) (2 * S) (scopeCallbackBound S) hrecord hcallback
  simp only [List.length_map] at hr
  have hr' : RecordPrograms.budget (SubexpChunkRecordMap.callbackCost ell)
      (codes.map Encoding.encodeNat) ≤ S * (12 * S + scopeCallbackBound S + 7) := by
    rw [show 6 * (2 * S) = 12 * S by omega] at hr
    exact hr.trans (Nat.mul_le_mul_right _ hcodes)
  have hm := Encoding.length_encodeList_upper Encoding.encodeNat
    (codes.map (SubexpChunkRecordMap.chunk ell)) (S + 1) (by
      intro j hj
      obtain ⟨code, hc, rfl⟩ := List.mem_map.mp hj
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right (hchunk code hc) 1)
  simp only [List.length_map] at hm
  have hm' : (Encoding.encodeList Encoding.encodeNat
      (codes.map (SubexpChunkRecordMap.chunk ell))).length ≤ mappedScopeBytesBound S :=
    hm.trans (by unfold mappedScopeBytesBound; gcongr)
  change 5 + RecordPrograms.budget (SubexpChunkRecordMap.callbackCost ell)
    (codes.map Encoding.encodeNat) + 10 * _ + 120 * (_ + 1) ^ 2 ≤ _
  unfold scopeProgramBound
  gcongr

theorem scope_count_le {D : ℕ} (scope : List (Fin D)) (width S : ℕ)
    (hD : D ≤ S) (hlen : scope.length ≤ S) (hw : width ≤ S) :
    SubexpScopeCountSetup.commandBound width ((scope.map Fin.val).map Encoding.encodeNat) ≤
      countScopeBound S := by
  let records := (scope.map Fin.val).map Encoding.encodeNat
  have hl : records.length ≤ S := by simpa [records] using hlen
  have hs : ∀ w ∈ records, w.length ≤ S := by
    intro w hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    rw [Encoding.length_encodeNat]
    have := i.isLt
    omega
  have he := Encoding.length_encodeList_upper id records S hs
  have he' : (Encoding.encodeList id records).length ≤ scopeBytesBound S :=
    he.trans (by unfold scopeBytesBound; gcongr)
  have hsum : (records.map List.length).sum ≤ S * S :=
    (sum_lengths_le records S hs).trans (Nat.mul_le_mul_right S hl)
  have hf : SubexpFactorCountSetup.budget width records.length ≤
      SubexpFactorCountSetup.budget S S := by
    unfold SubexpFactorCountSetup.budget SubexpFactorCountSetup.countBudget
    gcongr
  change 7 * (Encoding.encodeList id records).length + 5 +
    (4 * (records.map List.length).sum + 6 * records.length + 5) +
    SubexpFactorCountSetup.budget width records.length + 1 ≤ _
  unfold countScopeBound
  gcongr

theorem candidate_cost_le {n : ℕ} (ls : List (SAT.Literal (Fin n))) (padding S : ℕ)
    (hn : n ≤ S) (hlen : ls.length ≤ S) (hpad : padding ≤ S * S) :
    SubexpCandidateRowProgram.workCost ls padding ≤ candidateBound S := by
  have hc := clause_bytes_le ls S hn hlen
  have hr := (row_cost_le ls S hn).trans (Nat.mul_le_mul_right _ hlen)
  unfold SubexpCandidateRowProgram.workCost candidateBound
  gcongr

theorem field_callback_le {D n : ℕ} (c : SubexpClauseFactorProgram.Inputs)
    (scope : List (Fin D)) (ls : List (SAT.Literal (Fin n))) (rank S : ℕ)
    (hmod : c.modulus.length ≤ S) (hell : c.ellShape.length ≤ S)
    (hwidth : c.widthShape.length ≤ S) (hfull : c.fullShape.length ≤ S * S)
    (hnshape : c.nShape.length ≤ S) (hD : D ≤ S) (hn : n ≤ S)
    (hlen : ls.length ≤ S) (hscope : scope.length ≤ S) (hrank : rank ≤ S) :
    SubexpFieldTableEnumeration.callbackBound (SubexpClauseFactorProgram.tableMasters c scope)
      scope ls rank ≤ fieldCallbackBound S := by
  have hbytes := Encoding.length_encodeList_upper Encoding.encodeNat (scope.map Fin.val) S (by
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    rw [Encoding.length_encodeNat]
    have := i.isLt
    omega)
  simp only [List.length_map] at hbytes
  have hs : (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)).length ≤ scopeBytesBound S :=
    hbytes.trans (by unfold scopeBytesBound; gcongr)
  have hc := candidate_cost_le ls (c.fullShape.length - n) S hn hlen
    ((Nat.sub_le _ _).trans hfull)
  unfold SubexpFieldTableEnumeration.callbackBound SubexpClauseFactorProgram.tableMasters
    SubexpClauseFactorProgram.fieldMasters fieldCallbackBound
  simp only [List.length_replicate]
  gcongr

theorem unit_cost_le {D n : ℕ} (c : SubexpClauseFactorProgram.Inputs)
    (scope : List (Fin D)) (ls : List (SAT.Literal (Fin n))) (S : ℕ)
    (hmod : c.modulus.length ≤ S) (hbinary : c.binaryEll.length ≤ S)
    (hell : c.ellShape.length ≤ S) (hwidth : c.widthShape.length ≤ S)
    (hfull : c.fullShape.length ≤ S * S) (hnshape : c.nShape.length ≤ S)
    (hclause : c.clause = SubexpClauseRowProgram.clauseBytes ls)
    (hD : D ≤ S) (hn : n ≤ S) (hlen : ls.length ≤ S) (hscope : scope.length ≤ S)
    (hcount : SubexpClauseFactorProgram.rowCount c scope ≤ S) :
    SubexpClauseFactorProgram.budget c scope ls ≤ unitBound S := by
  have hc : c.clause.length ≤ clauseBytesBound S := by
    rw [hclause]; exact clause_bytes_le ls S hn hlen
  have hs := scope_program_le c.binaryEll ls S hbinary hn hlen
  have hsc := scope_count_le scope c.modulus.length S hD hscope hmod
  have hfuel : SubexpClauseFactorProgram.fuelWidth c scope ≤ fuelWidthBound S := by
    unfold SubexpClauseFactorProgram.fuelWidth fuelWidthBound
    gcongr
  have hcb := field_callback_le c scope ls (SubexpClauseFactorProgram.rowCount c scope) S
    hmod hell hwidth hfull hnshape hD hn hlen hscope hcount
  have he : SubexpFieldTableEnumeration.enumerationBound
      (SubexpClauseFactorProgram.tableMasters c scope) scope ls
      (SubexpClauseFactorProgram.rowCount c scope) (SubexpClauseFactorProgram.fuelWidth c scope) ≤
      enumerationBound S := by
    unfold SubexpFieldTableEnumeration.enumerationBound enumerationBound
    gcongr
  unfold SubexpClauseFactorProgram.budget unitBound
  gcongr

theorem callback_cost_le {D n : ℕ} (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c D n) (ls : List (SAT.Literal (Fin n))) (S : ℕ)
    (hmod : c.modulus.length ≤ S) (hbinary : c.binaryEll.length ≤ S)
    (hell : c.ellShape.length ≤ S) (hD : D ≤ S) (hn : n ≤ S) (hlen : ls.length ≤ S)
    (hcount : BinaryArithmetic.toNat c.modulus ^
      (SubexpClauseFamilyCallback.scope c hv ls).length ≤ S) :
    SubexpClauseFamilyCallback.callbackCost c hv ls ≤ callbackBound S := by
  have hscope := (SubexpClauseFamilyCallback.scope_length_le c hv ls).trans hlen
  have hfull : c.fullShape.length ≤ S * S := by rw [hv.full]; exact Nat.mul_le_mul hD hell
  have hu := unit_cost_le (SubexpClauseFamilyCallback.withClause c ls)
    (SubexpClauseFamilyCallback.scope c hv ls) ls S hmod hbinary hell
    (by change c.widthShape.length ≤ S; rw [hv.width]; exact hmod) hfull
    (by change c.nShape.length ≤ S; rw [hv.shape]; exact hn) rfl hD hn hlen hscope hcount
  have hc := clause_bytes_le ls S hn hlen
  have ht : (SubexpClauseFamilyCallback.table c hv ls).length ≤ S := by
    rw [SubexpClauseFamilyCallback.table_length]; exact hcount
  have hs : (SubexpClauseFamilyCallback.scopeBytes c ls).length ≤ scopeBytesBound S :=
    (SubexpClauseFamilyCallback.scopeBytes_length_le c hv ls).trans
      (by unfold scopeBytesBound; gcongr)
  change SubexpClauseFamilyCallback.unitCost c hv ls ≤ unitBound S at hu
  unfold SubexpClauseFamilyCallback.callbackCost callbackBound
  gcongr

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
