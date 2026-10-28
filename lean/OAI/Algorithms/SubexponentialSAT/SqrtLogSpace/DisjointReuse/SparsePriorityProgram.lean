import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
import OAI.Algorithms.SubexponentialSAT.CoreMaskProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.PowerPrograms
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseControllerProgram

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RecordSearch
open OAI.Algorithms.SubexponentialSAT.RecordPrograms StructuredCalls

theorem loop_run_with_miss_invariant {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : ∀ (bits tail : List Bool) (base : State r s),
      validPayload bits → invariant base →
      ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧
        (test bits = false → invariant next) ∧ effect bits base next ∧
        Eval callback n (state p base false true false tail bits.reverse)
          (state p next false true (test bits) tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ (records.any test = false → invariant next) ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], (fun _ => valid), Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ :=
        contract bits tail base (validRecords bits (by simp)) valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, (by simp [ht]),
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ :=
            ih middle (fun item hi => validRecords item (by simp [hi])) (hmiddle ht)
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, (by simpa [ht] using hnext),
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

theorem iterate_run_with_miss_invariant {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : ∀ (bits tail : List Bool) (base : State r s),
      validPayload bits → invariant base →
      ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧
        (test bits = false → invariant next) ∧ effect bits base next ∧
        Eval callback n (state p base false true false tail bits.reverse)
          (state p next false true (test bits) tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ (records.any test = false → invariant next) ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with_miss_invariant p callback test cost invariant effect validPayload contract
      records suffix base validRecords valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RecordSearch


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

theorem length_perm {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Perm ys) :
    (Encoding.encodeList enc xs).length = (Encoding.encodeList enc ys).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b xs => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem length_reverse {α : Type*} (enc : α → List Bool) (xs : List α) :
    (Encoding.encodeList enc xs.reverse).length = (Encoding.encodeList enc xs).length :=
  length_perm enc (List.reverse_perm xs)

theorem length_le_of_sublist {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Sublist ys) :
    (Encoding.encodeList enc xs).length ≤ (Encoding.encodeList enc ys).length := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a h ih =>
      rw [Encoding.length_encodeList_cons]
      omega
  | cons_cons a h ih =>
      rw [Encoding.length_encodeList_cons, Encoding.length_encodeList_cons]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

abbrev Clause := List (List Bool)
abbrev Formula := List Clause

/-- Raw-list specification of the selected family; all runtime tests are bit programs below. -/
def selectedRaw {α : Type*} [DecidableEq α] (F : List (List α)) (c : ℕ)
    (H : List α) : List (List α) :=
  F.filter fun C => decide (C.length = c) && ExecCNF.subset H C

theorem selectedRaw_subset {α : Type*} [DecidableEq α]
    (F : List (List α)) (c : ℕ) (H : List α) : selectedRaw F c H ⊆ F :=
  List.filter_sublist.subset

theorem selectedRaw_length_le {α : Type*} [DecidableEq α]
    (F : List (List α)) (c : ℕ) (H : List α) : (selectedRaw F c H).length ≤ F.length :=
  List.length_filter_le _ _

theorem selectedRaw_set {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (selectedRaw F c H) =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  ext D
  simp only [ExecCNF.mem_formulaSet, DisjointBranch.mem_selected]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCF, htest⟩ := List.mem_filter.mp hC
    obtain ⟨hc, hsub⟩ := Bool.and_eq_true_iff.mp htest
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨⟨C, hCF, rfl⟩, hcard.trans (of_decide_eq_true hc),
      (ExecCNF.subset_true H C).mp hsub⟩
  · rintro ⟨⟨C, hCF, rfl⟩, hc, hsub⟩
    refine ⟨C, List.mem_filter.mpr ⟨hCF, ?_⟩, rfl⟩
    apply Bool.and_eq_true_iff.mpr
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨decide_eq_true (hcard.symm.trans hc), (ExecCNF.subset_true H C).mpr hsub⟩

theorem selectedRaw_length {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    (selectedRaw F c H).length =
      SparsePriority.degree (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hn : ((selectedRaw F c H).map ExecCNF.clauseSet).Nodup :=
    (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hdistinct
  have hc := List.toFinset_card_of_nodup hn
  change (ExecCNF.formulaSet (selectedRaw F c H)).card = _ at hc
  rw [selectedRaw_set F c H hF, List.length_map] at hc
  exact hc.symm

theorem selectedRaw_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (F : List (List α)) (c : ℕ) (H : List α) :
    selectedRaw (F.map (List.map f)) c (H.map f) = (selectedRaw F c H).map (List.map f) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    cases h : decide (C.length = c) && ExecCNF.subset H C <;>
      simp [selectedRaw, List.length_map,
        ExecClauseRelationsProgram.subset_map_injective f hf, h] at ih ⊢
    all_goals exact ih

/-- All masks have fixed length `k`; the finite control table depends only on `k`. -/
def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (masks k).map (false :: ·) ++ (masks k).map (true :: ·)

@[simp] theorem mem_masks (mask : List Bool) (k : ℕ) : mask ∈ masks k ↔ mask.length = k := by
  induction k generalizing mask with
  | zero => simp [masks]
  | succ k ih =>
    cases mask with
    | nil => simp [masks]
    | cons b mask => cases b <;> simp [masks, ih]

@[simp] theorem masks_length (k : ℕ) : (masks k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [masks, ih, pow_succ, Nat.mul_comm, two_mul]

def masked {α : Type*} : List Bool → List α → List α
  | _, [] => []
  | mask, x :: xs => if mask.headD false then x :: masked mask.tail xs else masked mask.tail xs

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem masked_map {α β : Type*} (f : α → β) (mask : List Bool) (C : List α) :
    masked mask (C.map f) = (masked mask C).map f := by
  induction C generalizing mask with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, masked]; split <;> simp [ih]

theorem masked_words (mask : List Bool) (C : Clause) :
    masked mask C = CoreMaskProgram.select mask C := by
  induction C generalizing mask with
  | nil => rfl
  | cons x xs ih => simp only [masked, CoreMaskProgram.select]; split <;> simp [ih]

theorem masked_membership {α : Type*} [DecidableEq α] (C : List α) (H : Finset α)
    (suffix : List Bool) :
    masked (C.map (fun x => decide (x ∈ H)) ++ suffix) C = C.filter (fun x => decide (x ∈ H)) := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ H <;> simp [masked, hx, ih]

theorem exists_masked {α : Type*} [DecidableEq α] (k : ℕ) (C : List α) (H : Finset α)
    (hC : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ mask ∈ masks k, (masked mask C).toFinset = H := by
  let mask := C.map (fun x => decide (x ∈ H)) ++ List.replicate (k - C.length) false
  refine ⟨mask, (mem_masks mask k).mpr ?_, ?_⟩
  · simp [mask, Nat.add_sub_of_le hC]
  · rw [show masked mask C = C.filter (fun x => decide (x ∈ H)) from masked_membership C H _]
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨by simpa using hH h, h⟩⟩

def rawCandidates {α : Type*} (k : ℕ) (F : List (List α)) : List (ℕ × List α) :=
  F.flatMap fun C => (masks k).map fun mask => (C.length, masked mask C)

theorem rawCandidates_length {α : Type*} (k : ℕ) (F : List (List α)) :
    (rawCandidates k F).length = F.length * 2 ^ k := by
  simp [rawCandidates, List.length_flatMap]

theorem rawCandidates_complete {α : Type*} [DecidableEq α]
    (k : ℕ) (F : List (List α)) (C : List α) (H : Finset α)
    (hC : C ∈ F) (hwidth : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ core, (C.length, core) ∈ rawCandidates k F ∧ core.toFinset = H ∧ core.Sublist C := by
  obtain ⟨mask, hm, he⟩ := exists_masked k C H hwidth hH
  refine ⟨masked mask C, ?_, he, masked_sublist mask C⟩
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨mask, hm, rfl⟩⟩

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

theorem represent_core {n : ℕ} (k : ℕ) (F : List (List (SAT.Literal (Fin n))))
    (c : ℕ) (H : SAT.Clause (Fin n))
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdegree : 0 < SparsePriority.degree (ExecCNF.formulaSet F) c H) :
    ∃ core, (c, core) ∈ rawCandidates k F ∧ ExecCNF.clauseSet core = H ∧ core.length = H.card := by
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hdegree
  obtain ⟨hCF, hc, hH⟩ := DisjointBranch.mem_selected.mp hC
  obtain ⟨rawC, hrawC, rfl⟩ := ExecCNF.mem_formulaSet.mp hCF
  have hrawlen : rawC.length = c :=
    (List.toFinset_card_of_nodup (hnodup rawC hrawC)).symm.trans hc
  obtain ⟨core, hcore, he, hsub⟩ :=
    rawCandidates_complete k F rawC H hrawC (hwidth rawC hrawC) hH
  have hnodupCore := hsub.nodup (hnodup rawC hrawC)
  refine ⟨core, hrawlen ▸ hcore, he, ?_⟩
  exact (List.toFinset_card_of_nodup hnodupCore).symm.trans (congrArg Finset.card he)

/-- Source-level negative evidence obtained after every finite candidate fails. -/
theorem select_none_of_raw_failure {n : ℕ} (k : ℕ)
    (F : List (List (SAT.Literal (Fin n)))) (M : ℕ) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hfail : ∀ c core, (c, core) ∈ rawCandidates k F → 0 < core.length → core.length < c →
      (selectedRaw F c core).length < M ^ (c - core.length)) :
    SparsePriority.select (ExecCNF.formulaSet F) M = none := by
  apply SparsePriority.select_eq_none_of_degrees
  intro c H hH hc
  by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c H = 0
  · rw [hz]
    exact pow_pos hM _
  obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c H hwidth hnodup (Nat.pos_of_ne_zero hz)
  have hf := hfail c core hcore (by omega) (by omega)
  simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

/-- A scan certificate records only tested candidates and preceding failed tests. -/
structure RawPriority {α : Type*} [DecidableEq α] (k : ℕ) (F : List (List α))
    (M c : ℕ) (H : List α) : Prop where
  candidate : (c, H) ∈ rawCandidates k F
  core_nonempty : 0 < H.length
  core_proper : H.length < c
  threshold : M ^ (c - H.length) ≤ (selectedRaw F c H).length
  minimum : ∀ d core, (d, core) ∈ rawCandidates k F → 0 < core.length → core.length < d →
    d < c → (selectedRaw F d core).length < M ^ (d - core.length)
  maximum : ∀ core, (c, core) ∈ rawCandidates k F → H.length < core.length → core.length < c →
    (selectedRaw F c core).length < M ^ (c - core.length)

theorem RawPriority.toPriority {n : ℕ} {k : ℕ} {F : List (List (SAT.Literal (Fin n)))}
    {M c : ℕ} {H : List (SAT.Literal (Fin n))} (h : RawPriority k F M c H) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    SparsePriority.Priority (ExecCNF.formulaSet F) M c (ExecCNF.clauseSet H) := by
  obtain ⟨C, hCF, hc, hsub⟩ := rawCandidate_spec k F c H h.candidate
  have hHnodup := hsub.nodup (hnodup C hCF)
  have hHcard : (ExecCNF.clauseSet H).card = H.length := List.toFinset_card_of_nodup hHnodup
  have hCcard : (ExecCNF.clauseSet C).card = c :=
    (List.toFinset_card_of_nodup (hnodup C hCF)).trans hc
  refine ⟨⟨ExecCNF.clauseSet C, ExecCNF.mem_formulaSet.mpr ⟨C, hCF, rfl⟩, hCcard, ?_⟩,
    hHcard.symm ▸ h.core_nonempty, hHcard.symm ▸ h.core_proper, ?_, ?_, ?_⟩
  · intro l hl
    exact ExecCNF.mem_clauseSet.mpr (hsub.subset (ExecCNF.mem_clauseSet.mp hl))
  · simpa only [hHcard, selectedRaw_length F c H hnodup hdistinct] using h.threshold
  · intro d S hS hSd hdc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) d S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F d S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.minimum d core hcore (by omega) (by omega) hdc
    simpa only [selectedRaw_length F d core hnodup hdistinct, he, hlen] using hf
  · intro S hHS hSc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.maximum core hcore (by omega) (by omega)
    simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

namespace Guard

abbrev Data := State 13 11

def widthStack : Fin 9 → Fin 11 := ![0, 1, 2, 10, 4, 5, 6, 7, 3]
def subsetReg : Fin 12 → Fin 13 := Fin.castAdd 1
def subsetStack : Fin 10 → Fin 11 := Fin.castAdd 1

theorem widthStack_injective : Function.Injective widthStack := by decide

theorem subsetReg_injective : Function.Injective subsetReg := Fin.castAdd_injective 12 1

theorem subsetStack_injective : Function.Injective subsetStack := Fin.castAdd_injective 10 1

/-- Only input-sized words are copied: the clause, its width, and the core. -/
def copyClause : Cmd 13 11 := .call (StackRoutines.copyProgram 9 5 0 0 1)

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 5 (d.stacks 9)⟩

theorem copyClause_eval (d : Data) (h0 : d.stacks 0 = []) (h5 : d.stacks 5 = []) :
    Eval copyClause (7 * (d.stacks 9).length + 5) d (copied d) := by
  have h := ListRegisterProgram.copy_run (r := 13) (s := 11) 9 5 0 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h0
  apply Eval.call
  simpa [copied, StackRoutines.copyStacks, h5] using h

def width : Cmd 13 11 :=
  liftCommand (SparsePriorityPrimitives.Count.countTest 0) 5 5 id widthStack

def subset : Cmd 13 11 :=
  liftCommand (ExecClauseRelationsProgram.compare 0 1) 8 9 subsetReg subsetStack

/-- The core is on stack 8, clause on 9, and exact binary width on 10.
All eight work stacks are empty at both boundaries; register 12 receives the result. -/
def command : Cmd 13 11 :=
  .seq copyClause (.seq width (.seq (.base (.atom (.copy 12 4)))
    (.seq subset (.base (.atom (.band 12 12 9))))))

theorem width_eval (C : Clause) (d : Data)
    (h5 : d.stacks 5 = Encoding.encodeList id C)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h3 : d.stacks 3 = []) :
    ∃ t ≤ 200 * ((Encoding.encodeList id C).length + (d.stacks 10).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval width t d e ∧
        e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) := by
  let a := projectState id widthStack d
  obtain ⟨t, ht, b, hb, hbs, hbr, _⟩ :=
    SparsePriorityPrimitives.Count.countTest_eval 0 C a h5 h6 h7 h3
  let e := embedState id widthStack d b
  have he := eval_liftCommand_from_state (SparsePriorityPrimitives.Count.countTest 0) 5 5
    id widthStack d Function.injective_id widthStack_injective hb
  refine ⟨t + 1, by simpa [a, projectState, SparsePriorityPrimitives.Count.expectedPort,
    widthStack] using Nat.add_le_add_right ht 1, e, he, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, widthStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ widthStack_injective j, hbs]
      fin_cases j <;> simp [a, projectState, widthStack]
    · rw [embedState_stack_frame _ _ _ _ _ hi]
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · exact (embedState_register id widthStack d b Function.injective_id 4).trans hbr

theorem subset_eval (H C : Clause) (d : Data)
    (hH : d.stacks 8 = Encoding.encodeList id H)
    (hC : d.stacks 9 = Encoding.encodeList id C)
    (hwork : ∀ i : Fin 8, d.stacks (Fin.castAdd 3 i) = []) :
    ∃ t ≤ ExecClauseRelationsProgram.compareBound H C + 1,
      ∃ e : Data, Eval subset t d e ∧ e.stacks = d.stacks ∧
        e.regs 9 = ExecCNF.subset H C ∧ e.regs 12 = d.regs 12 := by
  let a := projectState subsetReg subsetStack d
  have ha : ExecClauseRelationsProgram.clean a := hwork
  obtain ⟨t, ht, b, hb, hclean, hresult, hframe, _, _⟩ :=
    ExecClauseRelationsProgram.compare_eval H C 0 1 a hH hC ha
  let e := embedState subsetReg subsetStack d b
  have he := eval_liftCommand_from_state (ExecClauseRelationsProgram.compare 0 1) 8 9
    subsetReg subsetStack d subsetReg_injective subsetStack_injective hb
  refine ⟨t + 1, Nat.add_le_add_right ht 1, e, he, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, subsetStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ subsetStack_injective j]
      fin_cases j
      · exact (hclean 0).trans (hwork 0).symm
      · exact (hclean 1).trans (hwork 1).symm
      · exact (hclean 2).trans (hwork 2).symm
      · exact (hclean 3).trans (hwork 3).symm
      · exact (hclean 4).trans (hwork 4).symm
      · exact (hclean 5).trans (hwork 5).symm
      · exact (hclean 6).trans (hwork 6).symm
      · exact (hclean 7).trans (hwork 7).symm
      · exact hframe 0
      · exact hframe 1
    · exact embedState_stack_frame _ _ _ _ _ hi
  · exact (embedState_register subsetReg subsetStack d b subsetReg_injective 9).trans hresult
  · exact embedState_register_frame _ _ _ _ _ (by decide)

theorem command_eval (H C : Clause) (d : Data)
    (hH : d.stacks 8 = Encoding.encodeList id H)
    (hC : d.stacks 9 = Encoding.encodeList id C)
    (hwork : ∀ i : Fin 8, d.stacks (Fin.castAdd 3 i) = []) :
    ∃ t ≤ 400 * ((Encoding.encodeList id H).length + (Encoding.encodeList id C).length +
        (d.stacks 10).length + 1) ^ 2,
      ∃ e : Data, Eval command t d e ∧ e.stacks = d.stacks ∧
        e.regs 12 = (decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) &&
          ExecCNF.subset H C) := by
  let a := copied d
  have ha5 : a.stacks 5 = Encoding.encodeList id C := by simp [a, copied, hC]
  have haw (i : Fin 8) (hi : i.val ≠ 5) : a.stacks (Fin.castAdd 3 i) = [] := by
    have hi' : Fin.castAdd 3 i ≠ (5 : Fin 11) := fun h => hi (congrArg Fin.val h)
    simpa [a, copied, hi'] using hwork i
  obtain ⟨t, ht, b, hb, hbs, hb4⟩ := width_eval C a ha5
    (haw 6 (by decide)) (haw 7 (by decide)) (haw 3 (by decide))
  have hbstate : b.stacks = d.stacks := by
    rw [hbs]
    funext i
    by_cases hi : i = 5
    · subst i; simpa using (hwork 5).symm
    · simp [a, copied, hi]
  let c := (StructuredProgram.Atom.copy (r := 13) (s := 11) 12 4).eval b
  have hcs : c.stacks = d.stacks := hbstate
  have hc12 : c.regs 12 = decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) := by
    simpa [c, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, a, copied] using hb4
  obtain ⟨u, hu, z, hz, hzs, hz9, hz12⟩ := subset_eval H C c
    (by simpa only [hcs] using hH) (by simpa only [hcs] using hC)
    (by simpa only [hcs] using hwork)
  let e := (StructuredProgram.Atom.band (r := 13) (s := 11) 12 12 9).eval z
  refine ⟨(7 * (d.stacks 9).length + 5) + (t + (1 + (u + 1))), ?_, e,
    (copyClause_eval d (hwork 0) (hwork 5)).seq
      (hb.seq ((Eval.base (.atom _ _)).seq (hz.seq (Eval.base (.atom _ _))))),
    hzs.trans hcs, ?_⟩
  · rw [hC]
    have ha10 : a.stacks 10 = d.stacks 10 := by simp [a, copied]
    rw [ha10] at ht
    unfold ExecClauseRelationsProgram.compareBound at hu
    let L := (Encoding.encodeList id H).length + (Encoding.encodeList id C).length +
      (d.stacks 10).length + 1
    have hwidth : (Encoding.encodeList id C).length + (d.stacks 10).length + 1 ≤ L := by omega
    have hcore : (Encoding.encodeList id H).length + 1 ≤ L := by omega
    have hclause : (Encoding.encodeList id C).length + 1 ≤ L := by omega
    have hsq := Nat.pow_le_pow_left hwidth 2
    have hprod := Nat.mul_le_mul hcore hclause
    have hL : 1 ≤ L := by omega
    have hLSq : L ≤ L ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right L hL
    have ht' : t ≤ 200 * L ^ 2 + 1 :=
      ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 200 hsq) 1)
    have hu' : u ≤ 80 * L ^ 2 + 1 := by
      apply hu.trans
      simpa only [Nat.mul_assoc, pow_two] using
        Nat.add_le_add_right (Nat.mul_le_mul_left 80 hprod) 1
    have hclauseSq : (Encoding.encodeList id C).length ≤ L ^ 2 :=
      (by omega : (Encoding.encodeList id C).length ≤ L).trans hLSq
    change _ ≤ 400 * L ^ 2
    omega
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hz12, hc12, hz9]

end Guard

namespace Filter

abbrev Regs := Fin 16 → Bool
abbrev Data := State 16 14

def clauseCode (C : Clause) : List Bool := Encoding.encodeList id C

def formulaCode (F : Formula) : List Bool := Encoding.encodeList clauseCode F

def result (F : Formula) (H : Clause) (width : List Bool) : Formula :=
  F.filter fun C => decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C

def state (regs : Regs) (core width source output payload clause : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], core, clause, width, source, output, payload]⟩

def guardReg : Fin 13 → Fin 16 := Fin.castAdd 3

def guardStack : Fin 11 → Fin 14 := Fin.castAdd 3

def guard : Cmd 16 14 := liftCommand Guard.command 9 9 guardReg guardStack

theorem guard_eval (H C : Clause) (width source output : List Bool) (regs : Regs) :
    ∃ t ≤ 400 * ((clauseCode H).length + (clauseCode C).length + width.length + 1) ^ 2 + 1,
      ∃ rf : Regs, Eval guard t
        (state regs (clauseCode H) width source output [] (clauseCode C))
        (state rf (clauseCode H) width source output [] (clauseCode C)) ∧
      rf 12 = (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) := by
  let d := state regs (clauseCode H) width source output [] (clauseCode C)
  let a := projectState guardReg guardStack d
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := Guard.command_eval H C a rfl rfl (by intro i; fin_cases i <;> rfl)
  let e := embedState guardReg guardStack d b
  have hr : Function.Injective guardReg := Fin.castAdd_injective 13 3
  have hs : Function.Injective guardStack := Fin.castAdd_injective 11 3
  have he := eval_liftCommand_from_state Guard.command 9 9 guardReg guardStack d hr hs hb
  have hes : e.stacks = d.stacks := by
    funext i
    by_cases hi : ∃ j, guardStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ hs j, hbs]
      rfl
    · exact embedState_stack_frame _ _ _ _ _ hi
  have heq : e = state e.regs (clauseCode H) width source output [] (clauseCode C) :=
    congrArg₂ StructuredProgram.State.mk rfl hes
  refine ⟨t + 1, Nat.add_le_add_right ht 1, e.regs, heq ▸ he, ?_⟩
  exact (embedState_register guardReg guardStack d b hr 12).trans hbr

def transfer (source target : Fin 14) : Cmd 16 14 :=
  .call (StackRoutines.transferProgram source target 0 1)

theorem transfer_in (regs : Regs) (core width source output bits : List Bool) :
    Eval (transfer 13 9) (3 * bits.length + 3)
      (state regs core width source output bits.reverse [])
      (state (readRegs regs 0 1 none) core width source output [] bits) := by
  have h := ListRegisterProgram.transfer_run (r := 16) (s := 14) 13 9 0 1
    (by decide) (by decide) regs (state regs core width source output bits.reverse []).stacks
  have hs : StackRoutines.transferStacks 13 9
      (state regs core width source output bits.reverse []).stacks =
      (state (readRegs regs 0 1 none) core width source output [] bits).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  apply Eval.call
  rw [hs] at h
  simpa [ListRegisterProgram.Run, state, StructuredProgram.State.withPC] using h

theorem transfer_out (regs : Regs) (core width source output bits : List Bool) :
    Eval (transfer 9 13) (3 * bits.length + 3)
      (state regs core width source output [] bits)
      (state (readRegs regs 0 1 none) core width source output bits.reverse []) := by
  have h := ListRegisterProgram.transfer_run (r := 16) (s := 14) 9 13 0 1
    (by decide) (by decide) regs (state regs core width source output [] bits).stacks
  have hs : StackRoutines.transferStacks 9 13
      (state regs core width source output [] bits).stacks =
      (state (readRegs regs 0 1 none) core width source output bits.reverse []).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  apply Eval.call
  rw [hs] at h
  simpa [ListRegisterProgram.Run, state, StructuredProgram.State.withPC] using h

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 13 v) 14 p) 15 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 13) (regs 14) (regs 15) = regs := by
  funext i
  by_cases h13 : i = 13 <;> by_cases h14 : i = 14 <;> by_cases h15 : i = 15 <;>
    simp_all [flags]

def emitReg : Fin 3 → Fin 16 := ![13, 14, 15]

def emitStack : Fin 4 → Fin 14 := ![11, 9, 12, 13]

theorem emitReg_injective : Function.Injective emitReg := by decide

theorem emitStack_injective : Function.Injective emitStack := by decide

def emit : Cmd 16 14 := .call
  (ProgramLinking.liftProgram SparsePriorityPrimitives.Filter.emitIfSelectedProgram emitReg emitStack)

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (core width source₀ output₀ payload₀ source output payload clause : List Bool) :
    embedState emitReg emitStack (state regs core width source₀ output₀ payload₀ [])
      (SparsePriorityPrimitives.Filter.filterState v p f source clause output payload) =
      state (flags regs v p f) core width source output payload clause := by
  apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective emitStack_injective
  · intro i; fin_cases i <;> simp [emitReg, flags, state, SparsePriorityPrimitives.Filter.filterState]
  · intro i hi
    have h13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨1, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h13, h14, h15]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h11 : i ≠ 11 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h12 : i ≠ 12 := fun h => hi ⟨2, h.symm⟩
    have h13 : i ≠ 13 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits core width source output : List Bool) :
    Eval emit (SparsePriorityPrimitives.Filter.emitIfSelectedSteps (regs 15) bits + 1)
      (state regs core width source output bits.reverse [])
      (state (flags regs false true false) core width source
        (if regs 15 then true :: (Encoding.frame bits ++ output) else output) [] []) := by
  have h := eval_call_lifted SparsePriorityPrimitives.Filter.emitIfSelectedProgram emitReg emitStack
    (state regs core width source output bits.reverse []) emitReg_injective emitStack_injective
    (SparsePriorityPrimitives.Filter.emitIfSelected_trace (regs 15) bits source [] output (regs 13) (regs 14))
  simpa only [embed_emit, flags_self, emit] using h

def callback : Cmd 16 14 := .seq (transfer 13 9) (.seq guard
  (.seq (.base (.atom (.copy 15 12))) (.seq (transfer 9 13) emit)))

def cost (H : Clause) (width bits : List Bool) : ℕ :=
  500 * ((clauseCode H).length + bits.length + width.length + 1) ^ 2

theorem callback_eval (H C : Clause) (width source output : List Bool) (regs : Regs) :
    ∃ t ≤ cost H width (clauseCode C), ∃ rf : Regs,
      rf 13 = false ∧ rf 14 = true ∧ rf 15 = false ∧
      Eval callback t
        (state regs (clauseCode H) width source output (clauseCode C).reverse [])
        (state rf (clauseCode H) width source
          (if decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
            then true :: (Encoding.frame (clauseCode C) ++ output) else output) [] []) := by
  obtain ⟨t, ht, rg, hg, hr⟩ := guard_eval H C width source output (readRegs regs 0 1 none)
  let selected := Function.update rg 15 (rg 12)
  have hset : Eval (.base (.atom (.copy 15 12))) 1
      (state rg (clauseCode H) width source output [] (clauseCode C))
      (state selected (clauseCode H) width source output [] (clauseCode C)) := .base (.atom _ _)
  let restored := readRegs selected 0 1 none
  have hs : restored 15 = (decide (C.length = BinaryArithmetic.toNat width) &&
      ExecCNF.subset H C) := by simp [restored, selected, readRegs, hr]
  have he := emit_eval restored (clauseCode C) (clauseCode H) width source output
  rw [hs] at he
  have hfull := (transfer_in regs (clauseCode H) width source output (clauseCode C)).seq
    (hg.seq (hset.seq ((transfer_out selected (clauseCode H) width source output (clauseCode C)).seq he)))
  refine ⟨_, ?_, flags restored false true false, by simp [flags], by simp [flags],
    by simp [flags], hfull⟩
  have hem := SparsePriorityPrimitives.Filter.emitIfSelected_steps_le
    (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) (clauseCode C)
  dsimp [cost]
  have hsquare := Nat.le_self_pow (by decide : 2 ≠ 0)
    ((clauseCode H).length + (clauseCode C).length + width.length + 1)
  omega

def ports : RecordPrograms.Ports 16 14 where
  tag := 13
  present := 14
  found := 15
  source := 11
  payload := 13
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem record_state (regs : Regs) (core width source output payload clause tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs core width source output payload clause)
      v p f tail bits = state (flags regs v p f) core width tail output bits clause := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ports, state]

structure Ready (H : Clause) (width : List Bool) (d : Data) : Prop where
  shape : ∃ regs source output payload,
    d = state regs (clauseCode H) width source output payload []

def decodeClause (bits : List Bool) : Option Clause := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then some fields else none

@[simp] theorem decodeClause_clauseCode (C : Clause) : decodeClause (clauseCode C) = some C := by
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords (ProgramEncoding.encodeRecords C)
    if rest.isEmpty then some fields else none) = some C
  simp

def keep (H : Clause) (width bits : List Bool) : Bool :=
  match decodeClause bits with
  | some C => decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
  | none => false

@[simp] theorem keep_clauseCode (H C : Clause) (width : List Bool) :
    keep H width (clauseCode C) =
      (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) := by
  simp [keep]

theorem callback_contract (H : Clause) (width : List Bool) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false) (cost H width)
      (Ready H width) (SparsePriorityPrimitives.Filter.FilterEffect 12 (keep H width))
      (fun bits => ∃ C : Clause, bits = clauseCode C) := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase.shape
  obtain ⟨t, ht, rf, h13, h14, h15, he⟩ :=
    callback_eval H C width tail output (flags regs false true false)
  let out := if decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
    then true :: (Encoding.frame (clauseCode C) ++ output) else output
  let next := state rf (clauseCode H) width [] out [] []
  have hf : flags rf false true false = rf := by
    simpa only [h13, h14, h15] using flags_self rf
  refine ⟨t, next, ht, ⟨rf, [], out, [], rfl⟩, ?_, ?_⟩
  · constructor
    simp [next, out, state]
  · simpa only [next, record_state, hf] using he

def records (F : Formula) : List (List Bool) := F.map clauseCode

theorem formulaCode_records (F : Formula) :
    formulaCode F = Encoding.encodeList id (records F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [formulaCode, records, Encoding.encodeList] using ih

theorem filter_records (F : Formula) (H : Clause) (width : List Bool) :
    (records F).filter (keep H width) = records (result F H width) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [records, result] at ih
    cases h : decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C <;>
      simp [records, result, h, ih]

def scan : Cmd 16 14 := RecordPrograms.iterate ports callback

theorem scan_eval (F : Formula) (H : Clause) (width : List Bool)
    (acc : List (List Bool)) (regs : Regs) :
    ∃ t ≤ 3 + RecordPrograms.budget (cost H width) (records F), ∃ rf : Regs,
      Eval scan t
        (state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] [])
        (state rf (clauseCode H) width []
          (Encoding.encodeList id ((records (result F H width)).reverse ++ acc)) [] []) := by
  let d := state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] []
  have hvalid : ∀ bits ∈ records F, ∃ C : Clause, bits = clauseCode C := by
    intro bits hb
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨C, rfl⟩
  obtain ⟨t, next, ht, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (cost H width) (Ready H width)
    (SparsePriorityPrimitives.Filter.FilterEffect 12 (keep H width))
    (fun bits => ∃ C : Clause, bits = clauseCode C) (callback_contract H width)
    (records F) [] d hvalid ⟨regs, _, _, [], rfl⟩ (regs 13) (regs 14) (regs 15)
  have hout := SparsePriorityPrimitives.Filter.filterVisits_result 12 (keep H width) hhistory acc
    (show d.stacks 12 = _ from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext.shape
  have hout' : output = Encoding.encodeList id ((records (result F H width)).reverse ++ acc) := by
    simpa [d, state, filter_records] using hout
  have hany : (records F).any (fun _ => false) = false := by simp
  refine ⟨t, ht, flags rf false true false, ?_⟩
  simpa only [scan, d, List.append_nil, record_state, flags_self, ← formulaCode_records,
    hany, SparsePriorityPrimitives.Filter.unread_false, hout'] using he


theorem member_length_le (records : List (List Bool)) (bits : List Bool) (h : bits ∈ records) :
    bits.length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rw [Encoding.length_encodeList_cons]
      simp only [id_eq]
      omega
    · exact (ih h).trans (by rw [Encoding.length_encodeList_cons]; omega)

theorem budget_le (records : List (List Bool)) (H : Clause) (width : List Bool) :
    3 + RecordPrograms.budget (cost H width) records ≤
      600 * ((clauseCode H).length + (Encoding.encodeList id records).length +
        width.length + 1) ^ 3 := by
  let L := (clauseCode H).length + (Encoding.encodeList id records).length + width.length + 1
  have hc : ∀ bits ∈ records, cost H width bits ≤ 0 * bits.length + 500 * L ^ 2 := by
    intro bits hb
    have hlen := member_length_le records bits hb
    simp only [Nat.zero_mul, Nat.zero_add, cost]
    exact Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by dsimp [L]; omega) 2)
  have hb := RecordPrograms.program_budget_le_input (cost H width) records 0 (500 * L ^ 2) hc
  change 4 + RecordPrograms.budget (cost H width) records ≤
    (0 + 500 * L ^ 2 + 17) * ((Encoding.encodeList id records).length + 1) at hb
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hinput : (Encoding.encodeList id records).length + 1 ≤ L := by dsimp [L]; omega
  have hm := Nat.mul_le_mul_left (500 * L ^ 2 + 17) hinput
  have hsq : 1 ≤ L ^ 2 := one_le_pow₀ hL
  change _ ≤ 600 * L ^ 3
  nlinarith

theorem scan_polynomial (F : Formula) (H : Clause) (width : List Bool)
    (acc : List (List Bool)) (regs : Regs) :
    ∃ t ≤ 600 * ((clauseCode H).length + (formulaCode F).length + width.length + 1) ^ 3,
      ∃ rf : Regs, Eval scan t
        (state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] [])
        (state rf (clauseCode H) width []
          (Encoding.encodeList id ((records (result F H width)).reverse ++ acc)) [] []) := by
  obtain ⟨t, ht, rf, he⟩ := scan_eval F H width acc regs
  refine ⟨t, ht.trans ?_, rf, he⟩
  simpa only [← formulaCode_records] using budget_le (records F) H width


def startOutput : Cmd 16 14 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 12 0)))

theorem startOutput_eval (regs : Regs) (core width source : List Bool) :
    Eval startOutput 2 (state regs core width source [] [] [])
      (state (Function.update regs 0 false) core width source [false] [] []) := by
  have h := (Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (r := 16) (s := 14) 0 false)
    (state regs core width source [] [] []))).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push 12 0)
      ((StructuredProgram.Atom.set 0 false).eval (state regs core width source [] [] []))))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

def command : Cmd 16 14 := .seq startOutput scan

theorem command_eval (F : Formula) (H : Clause) (width : List Bool) (regs : Regs) :
    ∃ t ≤ 600 * ((clauseCode H).length + (formulaCode F).length + width.length + 1) ^ 3 + 2,
      ∃ rf : Regs, Eval command t
        (state regs (clauseCode H) width (formulaCode F) [] [] [])
        (state rf (clauseCode H) width []
          (formulaCode ((result F H width).reverse)) [] []) := by
  obtain ⟨t, ht, rf, he⟩ := scan_polynomial F H width [] (Function.update regs 0 false)
  refine ⟨2 + t, by omega, rf, ?_⟩
  have hfull := (startOutput_eval regs (clauseCode H) width (formulaCode F)).seq he
  simpa [command, formulaCode_records, records, List.map_reverse] using hfull


end Filter

namespace CountThreshold

abbrev Data := SparsePriorityPrimitives.Tuple.Data

def command : Cmd 13 9 :=
  .seq (.call SparsePriorityPrimitives.Count.countProgram)
    (.seq SparsePriorityPrimitives.Count.toBinary
      (.seq (SparsePriorityPrimitives.Count.less 6 4)
        (.seq (.base (.atom (.bnot 4 0))) (SparsePriorityPrimitives.Tuple.clear 6))))

/-- Compare a scanned family's exact size with a binary threshold without expanding
that threshold to unary. The only unary count has length bounded by the input. -/
theorem command_eval (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 300 * ((Encoding.encodeList id records).length + (d.stacks 4).length + 1) ^ 2,
      ∃ e : Data, Eval command t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 4) ≤ records.length) := by
  let a := SparsePriorityPrimitives.Count.counted records d
  have ha7 : a.stacks 7 = Encoding.encodeNat records.length := by
    simp [a, SparsePriorityPrimitives.Count.counted]
  have ha5 : a.stacks 5 = [] := by simp [a, SparsePriorityPrimitives.Count.counted]
  have ha6 : a.stacks 6 = [] := by simpa [a, SparsePriorityPrimitives.Count.counted] using h6
  have ha8 : a.stacks 8 = [] := by simpa [a, SparsePriorityPrimitives.Count.counted] using h8
  obtain ⟨t, ht, bits, b, hb, hvalue, hlength, hbs, _⟩ :=
    SparsePriorityPrimitives.Count.toBinary_eval records.length a ha7 ha5 ha6 ha8
  have hb5 : b.stacks 5 = [] := by simp [hbs, a, SparsePriorityPrimitives.Count.counted]
  have hb6 : b.stacks 6 = bits := by simp [hbs]
  have hb7 : b.stacks 7 = [] := by simp [hbs]
  have hb8 : b.stacks 8 = [] := by simpa [hbs, a, SparsePriorityPrimitives.Count.counted] using h8
  have hb4 : b.stacks 4 = d.stacks 4 := by simp [hbs, a, SparsePriorityPrimitives.Count.counted]
  obtain ⟨u, hu, c, hc, hcs, hc0, _⟩ := SparsePriorityPrimitives.Count.less_eval 6 4 b
    (by decide) (by decide) hb5 hb7 hb8
  let z := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 0).eval c
  let e := SparsePriorityPrimitives.Tuple.cleared 6 z
  have hc6 : c.stacks 6 = bits := by simpa [hcs] using hb6
  have hz6 : z.stacks 6 = bits := hc6
  have hu' : u ≤ 20 * (bits.length + (d.stacks 4).length + 1) := by
    simpa only [hb6, hb4] using hu
  refine ⟨SubexpSunflowerProgram.CountRecords.steps records +
    (t + (u + (1 + (2 * (z.stacks 6).length + 3)))), ?_, e,
    (SparsePriorityPrimitives.Count.count_eval records d hin h7).seq
      (hb.seq (hc.seq ((Eval.base (.atom _ _)).seq (SparsePriorityPrimitives.Tuple.clear_eval 6 z)))),
    ?_, ?_⟩
  · rw [hz6]
    have hcount := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hrecords := Encoding.length_encodeList_lower id records
    have hrecords' : records.length ≤ (Encoding.encodeList id records).length := by omega
    have hbits : bits.length ≤ (Encoding.encodeList id records).length :=
      hlength.trans hrecords'
    let H := (Encoding.encodeList id records).length + (d.stacks 4).length + 1
    have hH : 1 ≤ H := by dsimp [H]; omega
    have hEH : (Encoding.encodeList id records).length ≤ H := by dsimp [H]; omega
    have hRH : records.length ≤ H := hrecords'.trans hEH
    have hBH : bits.length ≤ H := hbits.trans hEH
    have hsq : H ≤ H ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right H hH
    have hRsq : records.length ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hRH 2
    have hcount' : SubexpSunflowerProgram.CountRecords.steps records ≤ 7 * H ^ 2 := by
      have h7 := Nat.mul_le_mul_left 7 hsq
      omega
    rw [FrontendProgram.initializeBound_eq] at ht
    have ht' : t ≤ 32 * H ^ 2 := by
      have h8 := Nat.mul_le_mul_left 8 hRsq
      have h14 := Nat.mul_le_mul_left 14 (hRH.trans hsq)
      have h10 : 10 ≤ 10 * H ^ 2 := by omega
      omega
    have hsum : bits.length + (d.stacks 4).length + 1 ≤ H := by
      dsimp [H]
      omega
    have hu'' : u ≤ 20 * H ^ 2 :=
      (hu'.trans (Nat.mul_le_mul_left 20 hsum)).trans (Nat.mul_le_mul_left 20 hsq)
    have hclear : 1 + (2 * bits.length + 3) ≤ 6 * H ^ 2 := by
      have h6 := Nat.mul_le_mul_left 6 hsq
      omega
    change SubexpSunflowerProgram.CountRecords.steps records +
      (t + (u + (1 + (2 * bits.length + 3)))) ≤ 300 * H ^ 2
    omega
  · funext i
    fin_cases i <;>
      simp [e, z, SparsePriorityPrimitives.Tuple.cleared, StackRoutines.clearStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        hcs, hbs, a, SparsePriorityPrimitives.Count.counted, h6, h7]
  · have hnot : (!decide (records.length < BinaryArithmetic.toNat (d.stacks 4))) =
        decide (BinaryArithmetic.toNat (d.stacks 4) ≤ records.length) := by
      by_cases h : records.length < BinaryArithmetic.toNat (d.stacks 4)
      · simp [h, Nat.not_le_of_lt h]
      · have hh : BinaryArithmetic.toNat (d.stacks 4) ≤ records.length := by omega
        simp [h, hh]
    simpa [e, z, SparsePriorityPrimitives.Tuple.cleared, readRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
      StructuredProgram.State.ofCfg, execInstr, hc0, hb6, hb4, hvalue] using hnot

end CountThreshold

namespace ThresholdPower

/-- The exponent depends only on the fixed width/core-size pass, before input quantification. -/
def command (exponent : ℕ) : Cmd 8 9 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 exponent.bits)
    (.seq (.call PowerPrograms.program) (ArithmeticExpressionSupport.clearCmd 1))

theorem command_eval (exponent : ℕ) (base : List Bool) (regs : PowerPrograms.Regs) :
    ∃ t ≤ PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3,
      ∃ rf : PowerPrograms.Regs, ∃ word : List Bool,
        Eval (command exponent) t (PowerPrograms.state regs base [] [])
          (PowerPrograms.state rf base [] word) ∧
        BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
        word.length ≤ 1 + exponent * base.length := by
  obtain ⟨ra, ha⟩ := ArithmeticExpressionSupport.pushWord_eval
    (1 : Fin 9) exponent.bits (PowerPrograms.state regs base [] [])
  have hstart : (⟨ra, Function.update (PowerPrograms.state regs base [] []).stacks 1
      (exponent.bits ++ (PowerPrograms.state regs base [] []).stacks 1)⟩ : State 8 9) =
      PowerPrograms.state ra base exponent.bits [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [PowerPrograms.state, PowerPrograms.stackState]
  rw [hstart] at ha
  obtain ⟨d, hv, hl, hd0, _, hd1, hwork, t, ht, htrace⟩ :=
    PowerPrograms.run_value ra base exponent.bits
  have hc := ArithmeticExpressionSupport.clear_eval (1 : Fin 9) d
  have hfinish : (⟨readRegs d.regs 0 1 none, Function.update d.stacks 1 []⟩ : State 8 9) =
      PowerPrograms.state (readRegs d.regs 0 1 none) base [] (d.stacks 2) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [PowerPrograms.stackState, hd0]
    all_goals exact hwork _ (by decide)
  rw [hfinish] at hc
  refine ⟨2 * exponent.bits.length + (t + (2 * (d.stacks 1).length + 3)),
    by omega, readRegs d.regs 0 1 none, d.stacks 2, ha.seq ((Eval.call _ htrace).seq hc), ?_, ?_⟩
  · simpa only [ArithmeticExpressionSupport.bits_value] using hv
  · simpa only [ArithmeticExpressionSupport.bits_value] using hl

theorem runtime_polynomial (exponent : ℕ) (base : List Bool) :
    PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3 ≤
      (100 * (exponent + 1) ^ 2 + 20 * (exponent + 1) * (exponent.bits.length + 1) + 6) *
        (base.length + 1) ^ 2 := by
  simp only [PowerPrograms.runtimeBound, PowerPrograms.workBound,
    PowerPrograms.callbackBound, ArithmeticExpressionSupport.bits_value]
  have hsq : 1 ≤ (base.length + 1) ^ 2 := one_le_pow₀ (by omega)
  have hinner : 2 + (exponent + 1) * base.length ≤
      2 * (exponent + 1) * (base.length + 1) := by
    ring_nf
    omega
  have hmain := Nat.mul_le_mul_left (exponent * (50 * (base.length + 1))) hinner
  have hexp : exponent ≤ exponent + 1 := by omega
  have hmain' := Nat.mul_le_mul_right
    (100 * (exponent + 1) * (base.length + 1) ^ 2) hexp
  have htail : (exponent + 1) * (16 * exponent.bits.length + 16) +
      4 * exponent.bits.length + 6 ≤
      20 * (exponent + 1) * (exponent.bits.length + 1) + 6 := by
    ring_nf
    omega
  have hprod := Nat.mul_le_mul_left
    (20 * (exponent + 1) * (exponent.bits.length + 1) + 6) hsq
  nlinarith only [hmain, hmain', htail, hprod]

end ThresholdPower

namespace Mask

abbrev Regs := Fin 8 → Bool
abbrev Data := State 8 4

def state (regs : Regs) (source mask output : List Bool) : Data :=
  ⟨regs, ![source, mask, [], output]⟩

def regPort : Fin 4 → Fin 8 := Fin.castAdd 4

def applyMask : Cmd 8 4 := liftCommand (.call CoreMaskProgram.program) 0 3 regPort id

theorem applyMask_eval (C : Clause) (mask : List Bool) (regs : Regs) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 1, ∃ rf : Regs,
      Eval applyMask t (state regs (Encoding.encodeList id C) mask [])
        (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C))) := by
  obtain ⟨t, ht, he⟩ := CoreMaskProgram.call_eval C [] mask (regs 0) (regs 1) (regs 2) (regs 3)
  let d := state regs (Encoding.encodeList id C) mask []
  let b := CoreMaskProgram.state false false false false [] (mask.drop C.length) []
    (Encoding.encodeList id (CoreMaskProgram.select mask C))
  have hs : projectState regPort id d =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
        (Encoding.encodeList id C ++ []) mask [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [d, state,
        CoreMaskProgram.stackData]
  have hr : Function.Injective regPort := Fin.castAdd_injective 4 4
  have hl := eval_liftCommand_from_state (.call CoreMaskProgram.program) 0 3 regPort id d
    hr Function.injective_id (hs.symm ▸ he)
  let e := embedState regPort id d b
  have heq : e = state e.regs [] (mask.drop C.length)
      (Encoding.encodeList id (masked mask C)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    apply (Function.injective_id.extend_apply b.stacks d.stacks i).trans
    fin_cases i <;> simp [b, CoreMaskProgram.state, CoreMaskProgram.stackData, masked_words]
  exact ⟨t + 1, Nat.add_le_add_right ht 1, e.regs, heq ▸ hl⟩

def command (mask : List Bool) : Cmd 8 4 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 mask)
    (.seq applyMask (ArithmeticExpressionSupport.clearCmd 1))

theorem command_eval (C : Clause) (mask : List Bool) (regs : Regs) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 4 * mask.length + 4,
      ∃ rf : Regs, Eval (command mask) t (state regs (Encoding.encodeList id C) [] [])
        (state rf [] [] (Encoding.encodeList id (masked mask C))) := by
  obtain ⟨ra, ha⟩ := ArithmeticExpressionSupport.pushWord_eval
    (1 : Fin 4) mask (state regs (Encoding.encodeList id C) [] [])
  have ha' : Eval (ArithmeticExpressionSupport.pushWord 1 mask) (2 * mask.length)
      (state regs (Encoding.encodeList id C) [] []) (state ra (Encoding.encodeList id C) mask []) := by
    convert ha using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state]
  obtain ⟨t, ht, rf, he⟩ := applyMask_eval C mask ra
  have hc := ArithmeticExpressionSupport.clear_eval (1 : Fin 4)
    (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C)))
  have hc' : Eval (ArithmeticExpressionSupport.clearCmd 1)
      (2 * (mask.drop C.length).length + 3)
      (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C)))
      (state (readRegs rf 0 1 none) [] [] (Encoding.encodeList id (masked mask C))) := by
    convert hc using 1
    · simp [state]
    · apply congrArg₂ StructuredProgram.State.mk rfl
      funext i
      fin_cases i <;> simp [state]
  refine ⟨2 * mask.length + (t + (2 * (mask.drop C.length).length + 3)), ?_,
    readRegs rf 0 1 none, ha'.seq (he.seq hc')⟩
  simp only [List.length_drop]
  omega

end Mask

namespace Selector

abbrev Code := Cmd 24 24

/-- The primitive word operations use one fixed empty copy buffer. -/
def copy (source target : Fin 24) : Code :=
  .call (StackRoutines.copyProgram source target 8 0 1)

def transfer (source target : Fin 24) : Code :=
  .call (StackRoutines.transferProgram source target 0 1)

def move (source target : Fin 24) : Code := .seq (transfer source 8) (transfer 8 target)

def clear (port : Fin 24) : Code := .call (StackRoutines.clearProgram port 0 1)

def atom (op : StructuredProgram.Atom 24 24) : Code := .base (.atom op)

def load (port : Fin 24) (word : List Bool) : Code :=
  liftCommand (ArithmeticExpressionSupport.pushWord port word) port port (Fin.castAdd 16) id

def maskStack : Fin 4 → Fin 24 := ![10, 11, 8, 9]

def maskCall (mask : List Bool) : Code :=
  liftCommand (Mask.command mask) 0 3 (Fin.castAdd 16) maskStack

def filterStack : Fin 14 → Fin 24 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 16, 10, 12, 11]

def filterCall : Code := liftCommand Filter.command 11 12 (Fin.castAdd 8) filterStack

def sizeStack : Fin 9 → Fin 24 := ![0, 1, 2, 20, 17, 5, 6, 7, 8]

def sizeCall : Code :=
  liftCommand (SparsePriorityPrimitives.Count.countTest 0) 5 5 (Fin.castAdd 11) sizeStack

def thresholdStack : Fin 9 → Fin 24 := ![0, 1, 2, 3, 17, 5, 6, 7, 8]

def thresholdCall : Code :=
  liftCommand CountThreshold.command 5 5 (Fin.castAdd 11) thresholdStack

def powerStack : Fin 9 → Fin 24 := ![19, 10, 17, 0, 1, 2, 3, 4, 5]

def powerCall (exponent : ℕ) : Code :=
  liftCommand (ThresholdPower.command exponent) 0 2 (Fin.castAdd 16) powerStack

/-- A failed candidate leaves both output ports empty; a successful one retains
its core and selected family. The surrounding parser owns ports 14 and 15. -/
def prepareCandidate (mask : List Bool) : Code :=
  .seq (transfer 15 10) (.seq (maskCall mask) (.seq (copy 9 5) sizeCall))

def prepareCandidateBound (C : Clause) (mask size : List Bool) : ℕ :=
  3 * (Filter.clauseCode C).length + 3 +
    (CoreMaskProgram.runtimeBound C + 4 * mask.length + 5) +
    (7 * (Filter.clauseCode (masked mask C)).length + 5) +
    (200 * ((Filter.clauseCode (masked mask C)).length + size.length + 1) ^ 2 + 1)

def checkCandidate : Code :=
  .seq (copy 18 10) (.seq filterCall (.seq (copy 12 5) thresholdCall))

def selectedFamily (F : Formula) (H : Clause) (width : List Bool) : Formula :=
  (Filter.result F H width).reverse

def checkCandidateBound (F : Formula) (H : Clause) (width threshold : List Bool) : ℕ :=
  7 * (Filter.formulaCode F).length + 5 +
    (600 * ((Filter.clauseCode H).length + (Filter.formulaCode F).length + width.length + 1) ^ 3 + 3) +
    (7 * (Filter.formulaCode (selectedFamily F H width)).length + 5) +
    (300 * ((Filter.formulaCode (selectedFamily F H width)).length + threshold.length + 1) ^ 2 + 1)

def retainCandidate : Code :=
  .seq (atom (.copy 23 4)) (.ite 23 (.base .skip) (.seq (clear 9) (clear 12)))

def resetCandidateFlags : Code := .seq (atom (.set 21 false)) (atom (.set 22 true))

def testedCandidate (mask : List Bool) : Code :=
  .seq (prepareCandidate mask)
    (.seq (.ite 4 (.seq checkCandidate retainCandidate)
      (.seq (clear 9) (atom (.set 23 false)))) resetCandidateFlags)

def accepted (F : Formula) (C : Clause) (mask width size threshold : List Bool) : Bool :=
  decide ((masked mask C).length = BinaryArithmetic.toNat size) &&
    decide (BinaryArithmetic.toNat threshold ≤ (Filter.result F (masked mask C) width).length)

def candidateBound (F : Formula) (C : Clause) (mask width size threshold : List Bool) : ℕ :=
  prepareCandidateBound C mask size + checkCandidateBound F (masked mask C) width threshold +
    4 * (Filter.clauseCode (masked mask C)).length +
    2 * (Filter.formulaCode (selectedFamily F (masked mask C) width)).length + 20


def candidate (mask : List Bool) : Code := testedCandidate mask

def ports : RecordPrograms.Ports 24 24 where
  tag := 21
  present := 22
  found := 23
  source := 14
  payload := 15
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- All three parameters are encoded in finite control before the input is supplied. -/
def widthFamily (F : Formula) (width : List Bool) : Formula :=
  (Filter.result F [] width).reverse

def familyInit (width : List Bool) : Code :=
  .seq (load 9 [false]) (.seq (load 16 width) (.seq (copy 13 10)
    (.seq filterCall (.seq (clear 9) (move 12 18)))))

def familyInitBound (F : Formula) (width : List Bool) : ℕ :=
  3 + (2 * width.length + 1) + (7 * (Filter.formulaCode F).length + 5) +
    (600 * ((Filter.formulaCode F).length + width.length + 2) ^ 3 + 3) +
    5 + (6 * (Filter.formulaCode (widthFamily F width)).length + 6)

def parameterInit (exponent : ℕ) (size : List Bool) : Code :=
  .seq (load 20 size) (.seq (powerCall exponent) (copy 18 14))

def parameterInitBound (exponent : ℕ) (size base family : List Bool) : ℕ :=
  (2 * size.length + 1) +
    (PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 4) +
    (7 * family.length + 5)

def clearMany : List (Fin 24) → Code
  | [] => .base .skip
  | port :: rest => .seq (clear port) (clearMany rest)

def eraseWords (ports : List (Fin 24)) (store : Fin 24 → List Bool) : Fin 24 → List Bool :=
  fun i => if i ∈ ports then [] else store i

def cleanup : Code := clearMany [14, 18, 16, 20, 17]


def phase (width coreSize : ℕ) (mask : List Bool) : Code :=
  .seq (familyInit width.bits)
    (.seq (parameterInit (width - coreSize) coreSize.bits)
      (.seq (RecordPrograms.iterate ports (candidate mask)) cleanup))

def passes (k : ℕ) : List (ℕ × ℕ × List Bool) :=
  (List.range (k - 1)).flatMap fun i =>
    (List.range (i + 1)).flatMap fun j =>
      (masks k).map fun mask => (i + 2, i + 1 - j, mask)

theorem mem_passes (k c h : ℕ) (mask : List Bool) :
    (c, h, mask) ∈ passes k ↔ 2 ≤ c ∧ c ≤ k ∧ 1 ≤ h ∧ h < c ∧ mask.length = k := by
  simp only [passes, List.mem_flatMap, List.mem_range, List.mem_map, mem_masks]
  constructor
  · rintro ⟨i, hi, j, hj, m, hm, he⟩
    cases he
    exact ⟨by omega, by omega, by omega, by omega, hm⟩
  · rintro ⟨hc, hck, hh, hhc, hm⟩
    refine ⟨c - 2, by omega, c - 1 - h, by omega, mask, hm, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨by omega, by omega, True.intro⟩

theorem passes_pairwise (k : ℕ) :
    (passes k).Pairwise (fun p q => p.1 ≤ q.1 ∧ (p.1 = q.1 → q.2.1 ≤ p.2.1)) := by
  rw [passes, List.pairwise_flatMap]
  constructor
  · intro i hi
    rw [List.pairwise_flatMap]
    constructor
    · intro j hj
      rw [List.pairwise_map]
      exact List.pairwise_of_forall (by intros; exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩)
    · apply List.pairwise_lt_range.imp
      intro j j' hjj' p hp q hq
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hq
      exact ⟨Nat.le_refl _, by intro; dsimp; omega⟩
  · apply List.pairwise_lt_range.imp
    intro i i' hii' p hp q hq
    obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j', hj', hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hq
    exact ⟨by dsimp; omega, by dsimp; omega⟩

/-- Every strictly preferable width/core-size phase occurs before a winning phase,
independently of mask and clause ties within that phase. -/
theorem higher_priority_mem_before {k : ℕ} {before after : List (ℕ × ℕ × List Bool)}
    {winner candidate : ℕ × ℕ × List Bool}
    (hsplit : passes k = before ++ winner :: after) (hmem : candidate ∈ passes k)
    (hbetter : candidate.1 < winner.1 ∨
      candidate.1 = winner.1 ∧ winner.2.1 < candidate.2.1) :
    candidate ∈ before := by
  have horder := passes_pairwise k
  rw [hsplit, List.pairwise_append] at horder
  rw [hsplit, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hb | he | ha
  · exact hb
  · subst candidate
    omega
  · have hle := (List.pairwise_cons.mp horder.2.1).1 candidate ha
    rcases hbetter with hwidth | ⟨heq, hcore⟩
    · omega
    · have hc := hle.2 heq.symm
      omega


def chain (commands : List Code) : Code :=
  SparseCountProgram.Controller.firstHit 23 commands

/-- One finite ordinary Boolean-stack program for each fixed width bound.
The outstanding proof obligations concern this concrete code, not an oracle callback. -/
def command (k : ℕ) : Code :=
  .seq (atom (.set 23 false))
    (chain ((passes k).map fun p => phase p.1 p.2.1 p.2.2))

def program (k : ℕ) := compiled (command k) 13 12

abbrev Data := State 24 24

private theorem embed_stacks_eq {r s R S : ℕ} (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (d : State R S) (b : State r s)
    (hs : Function.Injective stack) (out : Fin S → List Bool)
    (hports : ∀ j, b.stacks j = out (stack j))
    (hframe : ∀ i, (¬ ∃ j, stack j = i) → d.stacks i = out i) :
    (embedState register stack d b).stacks = out := by
  funext i
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_stack register stack d b hs j).trans (hports j)
  · exact (embedState_stack_frame register stack d b i hi).trans (hframe i hi)

theorem copy_eval (source target : Fin 24) (d : Data)
    (hs : source ≠ target) (hs8 : source ≠ 8) (ht8 : (8 : Fin 24) ≠ target)
    (h8 : d.stacks 8 = []) (ht : d.stacks target = []) :
    Eval (copy source target) (7 * (d.stacks source).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks target (d.stacks source)⟩ := by
  have h := ListRegisterProgram.copy_run source target 8 (0 : Fin 24) 1
    hs hs8 ht8 (by decide) d.regs d.stacks h8
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, ht] using h

theorem transfer_eval (source target : Fin 24) (d : Data) (h : source ≠ target) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩ := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run source target (0 : Fin 24) 1 h (by decide)
    d.regs d.stacks

theorem clear_eval (port : Fin 24) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 24) 1 d.regs d.stacks

theorem move_eval (source target : Fin 24) (d : Data)
    (hs : source ≠ target) (hs8 : source ≠ 8) (ht8 : (8 : Fin 24) ≠ target)
    (h8 : d.stacks 8 = []) :
    Eval (move source target) (6 * (d.stacks source).length + 6) d
      ⟨readRegs (readRegs d.regs 0 1 none) 0 1 none,
        Function.update (Function.update d.stacks source []) target
          (d.stacks source ++ d.stacks target)⟩ := by
  let middle : Data := ⟨readRegs d.regs 0 1 none,
    StackRoutines.transferStacks source 8 d.stacks⟩
  have h := (transfer_eval source 8 d hs8).seq (transfer_eval 8 target middle ht8)
  have hm : (middle.stacks 8).length = (d.stacks source).length := by
    simp [middle, StackRoutines.transferStacks, h8]
  rw [hm] at h
  convert h using 1
  · rfl
  · omega
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    by_cases hit : i = target
    · subst i
      simp [middle, StackRoutines.transferStacks, h8, Ne.symm hs, Ne.symm ht8]
    by_cases his : i = source
    · subst i
      simp [middle, StackRoutines.transferStacks, h8, hs, hs8]
    by_cases hi8 : i = 8
    · subst i
      simp [middle, StackRoutines.transferStacks, h8, Ne.symm hs8, ht8]
    simp [middle, StackRoutines.transferStacks, h8, hit, his, hi8]

/-- Loading a fixed literal word touches only the low eight registers. -/
theorem load_eval (port : Fin 24) (word : List Bool) (d : Data) :
    ∃ e : Data, Eval (load port word) (2 * word.length + 1) d e ∧
      e.stacks = Function.update d.stacks port (word ++ d.stacks port) ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) id d
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval port word a
  let b : State 8 24 := ⟨rf, Function.update a.stacks port (word ++ a.stacks port)⟩
  let e := embedState (Fin.castAdd 16) id d b
  refine ⟨e, eval_liftCommand_from_state _ port port (Fin.castAdd 16) id d
    (Fin.castAdd_injective 8 16) Function.injective_id he, ?_, ?_⟩
  · funext i
    exact (embedState_stack _ _ _ _ Function.injective_id i)
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem maskStack_injective : Function.Injective maskStack := by decide

theorem maskCall_eval (mask : List Bool) (C : Clause) (d : Data)
    (h10 : d.stacks 10 = Encoding.encodeList id C) (h11 : d.stacks 11 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 4 * mask.length + 5, ∃ e : Data,
      Eval (maskCall mask) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 []) 9
        (Encoding.encodeList id (masked mask C)) ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) maskStack d
  have ha : a = Mask.state a.regs (Encoding.encodeList id C) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [maskStack, h10, h11, h8, h9]
  obtain ⟨t, ht, rf, he⟩ := Mask.command_eval C mask a.regs
  rw [← ha] at he
  let b := Mask.state rf [] [] (Encoding.encodeList id (masked mask C))
  let e := embedState (Fin.castAdd 16) maskStack d b
  refine ⟨t + 1, by omega, e, eval_liftCommand_from_state _ 0 3
    (Fin.castAdd 16) maskStack d (Fin.castAdd_injective 8 16) maskStack_injective he, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ maskStack_injective
    · intro j
      fin_cases j <;> simp [b, Mask.state, maskStack, h11, h8]
    · intro i hi
      have hi10 : i ≠ 10 := fun h => hi ⟨0, h.symm⟩
      have hi9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
      simp [hi10, hi9]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem sizeStack_injective : Function.Injective sizeStack := by decide

theorem sizeCall_eval (C : Clause) (d : Data)
    (h5 : d.stacks 5 = Encoding.encodeList id C)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 200 * ((Encoding.encodeList id C).length + (d.stacks 20).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval sizeCall t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (C.length = BinaryArithmetic.toNat (d.stacks 20)) ∧
        (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 11) sizeStack d
  obtain ⟨t, ht, b, he, hb, hv, _⟩ :=
    SparsePriorityPrimitives.Count.countTest_eval 0 C a h5 h6 h7 h8
  let e := embedState (Fin.castAdd 11) sizeStack d b
  refine ⟨t + 1, by simpa [a, projectState, sizeStack,
    SparsePriorityPrimitives.Count.expectedPort] using Nat.add_le_add_right ht 1,
    e, eval_liftCommand_from_state _ 5 5 (Fin.castAdd 11) sizeStack d
      (Fin.castAdd_injective 13 11) sizeStack_injective he, ?_, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ sizeStack_injective
    · intro j
      rw [hb]
      fin_cases j <;> simp [a, projectState, sizeStack]
    · intro i hi
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · exact (embedState_register _ _ _ _ (Fin.castAdd_injective 13 11) 4).trans hv
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem thresholdStack_injective : Function.Injective thresholdStack := by decide

theorem thresholdCall_eval (F : Formula) (d : Data)
    (h5 : d.stacks 5 = Filter.formulaCode F)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 300 * ((Filter.formulaCode F).length + (d.stacks 17).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval thresholdCall t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ F.length) ∧
        (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 11) thresholdStack d
  have hin : a.stacks 5 = Encoding.encodeList id (Filter.records F) := by
    simpa [a, projectState, thresholdStack, ← Filter.formulaCode_records] using h5
  obtain ⟨t, ht, b, he, hb, hv⟩ := CountThreshold.command_eval (Filter.records F) a hin
    (by simpa [a, projectState, thresholdStack] using h6)
    (by simpa [a, projectState, thresholdStack] using h7)
    (by simpa [a, projectState, thresholdStack] using h8)
  let e := embedState (Fin.castAdd 11) thresholdStack d b
  refine ⟨t + 1, by simpa [a, projectState, thresholdStack,
    ← Filter.formulaCode_records] using Nat.add_le_add_right ht 1,
    e, eval_liftCommand_from_state _ 5 5 (Fin.castAdd 11) thresholdStack d
      (Fin.castAdd_injective 13 11) thresholdStack_injective he, ?_, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ thresholdStack_injective
    · intro j
      rw [hb]
      fin_cases j <;> simp [a, projectState, thresholdStack]
    · intro i hi
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · simpa [e, a, projectState, thresholdStack, Filter.records, List.length_map] using
      (embedState_register _ _ _ _ (Fin.castAdd_injective 13 11) 4).trans hv
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem filterStack_injective : Function.Injective filterStack := by decide

theorem filterCall_eval (F : Formula) (H : Clause) (width : List Bool) (d : Data)
    (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
    (h10 : d.stacks 10 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    ∃ t ≤ 600 * ((Filter.clauseCode H).length + (Filter.formulaCode F).length +
      width.length + 1) ^ 3 + 3, ∃ e : Data,
      Eval filterCall t d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 []) 12
        (Filter.formulaCode ((Filter.result F H width).reverse)) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 8) filterStack d
  have ha : a = Filter.state a.regs (Filter.clauseCode H) width
      (Filter.formulaCode F) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [filterStack, h9, h16, h10, h11, h12]
    all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5 | exact hwork 6 | exact hwork 7 | exact hwork 8
  obtain ⟨t, ht, rf, he⟩ := Filter.command_eval F H width a.regs
  rw [← ha] at he
  let b := Filter.state rf (Filter.clauseCode H) width []
    (Filter.formulaCode ((Filter.result F H width).reverse)) [] []
  let e := embedState (Fin.castAdd 8) filterStack d b
  refine ⟨t + 1, by omega, e, eval_liftCommand_from_state _ 11 12
    (Fin.castAdd 8) filterStack d (Fin.castAdd_injective 16 8) filterStack_injective he, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ filterStack_injective
    · intro j
      fin_cases j <;> simp [b, Filter.state, filterStack, h9, h16, h11]
      all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5 | exact hwork 6 | exact hwork 7 | exact hwork 8
    · intro i hi
      have hi10 : i ≠ 10 := fun h => hi ⟨11, h.symm⟩
      have hi12 : i ≠ 12 := fun h => hi ⟨12, h.symm⟩
      simp [hi10, hi12]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem powerStack_injective : Function.Injective powerStack := by decide

theorem powerCall_eval (exponent : ℕ) (base : List Bool) (d : Data)
    (h19 : d.stacks 19 = base) (h10 : d.stacks 10 = []) (h17 : d.stacks 17 = [])
    (hwork : ∀ i : Fin 6, d.stacks (Fin.castAdd 18 i) = []) :
    ∃ t ≤ PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 4,
      ∃ word : List Bool, ∃ e : Data,
        Eval (powerCall exponent) t d e ∧ e.stacks = Function.update d.stacks 17 word ∧
        BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
        word.length ≤ 1 + exponent * base.length ∧
        (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) powerStack d
  have ha : a = PowerPrograms.state a.regs base [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [powerStack, PowerPrograms.stackState,
        h19, h10, h17]
    all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5
  obtain ⟨t, ht, rf, word, he, hv, hl⟩ := ThresholdPower.command_eval exponent base a.regs
  rw [← ha] at he
  let b := PowerPrograms.state rf base [] word
  let e := embedState (Fin.castAdd 16) powerStack d b
  refine ⟨t + 1, by omega, word, e, eval_liftCommand_from_state _ 0 2
    (Fin.castAdd 16) powerStack d (Fin.castAdd_injective 8 16) powerStack_injective he,
    ?_, hv, hl, ?_⟩
  · apply embed_stacks_eq _ _ _ _ powerStack_injective
    · intro j
      fin_cases j <;> simp [b, PowerPrograms.state, PowerPrograms.stackState,
        powerStack, h19, h10]
      all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5
    · intro i hi
      have hi17 : i ≠ 17 := fun h => hi ⟨2, h.symm⟩
      simp [hi17]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem prepareCandidate_eval (C : Clause) (mask : List Bool) (d : Data)
    (h15 : d.stacks 15 = (Filter.clauseCode C).reverse)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = [])
    (h11 : d.stacks 11 = []) :
    ∃ t ≤ prepareCandidateBound C mask (d.stacks 20), ∃ e : Data,
      Eval (prepareCandidate mask) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 15 []) 9
        (Filter.clauseCode (masked mask C)) ∧
      e.regs 4 = decide ((masked mask C).length = BinaryArithmetic.toNat (d.stacks 20)) ∧
      (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 15 10 d.stacks⟩
  have ha := transfer_eval 15 10 d (by decide)
  have has : a.stacks = Function.update (Function.update d.stacks 15 []) 10
      (Filter.clauseCode C) := by
    funext i
    simp [a, StackRoutines.transferStacks, h15, h10]
  have ha10 : a.stacks 10 = Filter.clauseCode C := by simp [has]
  have ha11 : a.stacks 11 = [] := by simp [has, h11]
  have ha8 : a.stacks 8 = [] := by simp [has, h8]
  have ha9 : a.stacks 9 = [] := by simp [has, h9]
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := maskCall_eval mask C a ha10 ha11 ha8 ha9
  have hbstate : b.stacks = Function.update (Function.update d.stacks 15 []) 9
      (Filter.clauseCode (masked mask C)) := by
    rw [hbs, has]
    funext i
    by_cases hi10 : i = 10
    · subst i; simp [h10]
    · simp [Function.update_apply, hi10, Filter.clauseCode]
  have hb9 : b.stacks 9 = Filter.clauseCode (masked mask C) := by simp [hbstate]
  have hb8 : b.stacks 8 = [] := by simp [hbstate, h8]
  have hb5 : b.stacks 5 = [] := by simp [hbstate, h5]
  let c : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 5 (b.stacks 9)⟩
  have hc := copy_eval 9 5 b (by decide) (by decide) (by decide) hb8 hb5
  have hc5 : c.stacks 5 = Filter.clauseCode (masked mask C) := by simp [c, hb9]
  have hc6 : c.stacks 6 = [] := by simp [c, hbstate, h6]
  have hc7 : c.stacks 7 = [] := by simp [c, hbstate, h7]
  have hc8 : c.stacks 8 = [] := by simp [c, hbstate, h8]
  have hc20 : c.stacks 20 = d.stacks 20 := by simp [c, hbstate]
  obtain ⟨u, hu, e, he, hes, hev, her⟩ := sizeCall_eval (masked mask C) c hc5 hc6 hc7 hc8
  refine ⟨3 * (d.stacks 15).length + 3 + (t + (7 * (b.stacks 9).length + 5 + u)),
    ?_, e, ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [hc20] at hu
    simp only [h15, List.length_reverse, hb9]
    unfold prepareCandidateBound
    simp only [Filter.clauseCode] at hu ⊢
    omega
  · rw [hes]
    funext i
    by_cases hi5 : i = 5
    · subst i; simp [h5]
    · simp [c, hbstate, hi5]
  · simpa only [hc20] using hev
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i (by omega)
    have hei := her i hi
    simpa [a, c, readRegs, hi0, hi1, hbi] using hei
theorem checkCandidate_eval (F : Formula) (H : Clause) (width : List Bool) (d : Data)
    (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
    (h18 : d.stacks 18 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    ∃ t ≤ checkCandidateBound F H width (d.stacks 17), ∃ e : Data,
      Eval checkCandidate t d e ∧
      e.stacks = Function.update d.stacks 12 (Filter.formulaCode (selectedFamily F H width)) ∧
      e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ (Filter.result F H width).length) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 10 (d.stacks 18)⟩
  have ha := copy_eval 18 10 d (by decide) (by decide) (by decide) (hwork 8) h10
  have ha9 : a.stacks 9 = Filter.clauseCode H := by simp [a, h9]
  have ha16 : a.stacks 16 = width := by simp [a, h16]
  have ha10 : a.stacks 10 = Filter.formulaCode F := by simp [a, h18]
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    have hi : Fin.castAdd 15 i ≠ (10 : Fin 24) := by
      intro h
      have hh := congrArg Fin.val h
      have := i.isLt
      change i.val = 10 at hh
      omega
    simpa [a, hi] using hwork i
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := filterCall_eval F H width a ha9 ha16 ha10 haw
    (by simpa [a] using h11) (by simpa [a] using h12)
  have hbstate : b.stacks = Function.update d.stacks 12
      (Filter.formulaCode (selectedFamily F H width)) := by
    rw [hbs]
    funext i
    by_cases hi10 : i = 10
    · subst i; simp [h10]
    · simp [a, Function.update_apply, hi10, selectedFamily]
  have hb12 : b.stacks 12 = Filter.formulaCode (selectedFamily F H width) := by simp [hbstate]
  have hb8 : b.stacks 8 = [] := by simpa [hbstate] using hwork 8
  have hb5 : b.stacks 5 = [] := by simpa [hbstate] using hwork 5
  let c : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 5 (b.stacks 12)⟩
  have hc := copy_eval 12 5 b (by decide) (by decide) (by decide) hb8 hb5
  have hc5 : c.stacks 5 = Filter.formulaCode (selectedFamily F H width) := by simp [c, hb12]
  have hc6 : c.stacks 6 = [] := by simpa [c, hbstate] using hwork 6
  have hc7 : c.stacks 7 = [] := by simpa [c, hbstate] using hwork 7
  have hc8 : c.stacks 8 = [] := by simpa [c, hbstate] using hwork 8
  have hc17 : c.stacks 17 = d.stacks 17 := by simp [c, hbstate]
  obtain ⟨u, hu, e, he, hes, hev, her⟩ :=
    thresholdCall_eval (selectedFamily F H width) c hc5 hc6 hc7 hc8
  refine ⟨7 * (d.stacks 18).length + 5 + (t + (7 * (b.stacks 12).length + 5 + u)),
    ?_, e, ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [hc17] at hu
    simp only [h18, hb12]
    unfold checkCandidateBound
    omega
  · rw [hes]
    funext i
    by_cases hi5 : i = 5
    · subst i; simpa using hwork 5
    · simp [c, hbstate, hi5]
  · simpa only [hc17, selectedFamily, List.length_reverse] using hev
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i hi
    have hei := her i (by omega)
    simpa [a, c, readRegs, hi0, hi1, hbi] using hei
theorem retainCandidate_eval (d : Data) :
    ∃ t ≤ 2 * ((d.stacks 9).length + (d.stacks 12).length) + 8, ∃ e : Data,
      Eval retainCandidate t d e ∧
      e.stacks = (if d.regs 4 then d.stacks else
        Function.update (Function.update d.stacks 9 []) 12 []) ∧
      e.regs 23 = d.regs 4 ∧
      (∀ i : Fin 24, 16 ≤ i.val → i ≠ 23 → e.regs i = d.regs i) := by
  let a : Data := ⟨Function.update d.regs 23 (d.regs 4), d.stacks⟩
  have ha : Eval (atom (.copy 23 4)) 1 d a := .base (.atom _ _)
  cases hb : d.regs 4 with
  | false =>
    let b : Data := ⟨readRegs a.regs 0 1 none, Function.update a.stacks 9 []⟩
    let e : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 12 []⟩
    have hclear := (clear_eval 9 a).seq (clear_eval 12 b)
    have hbranch := Eval.ite_false (yes := (.base .skip : Code))
      (test := (23 : Fin 24)) (by simp [a, hb]) hclear
    refine ⟨1 + ((2 * (a.stacks 9).length + 3 + (2 * (b.stacks 12).length + 3)) + 1),
      ?_, e, ha.seq hbranch, ?_, ?_, ?_⟩
    · simp [a, b]
      omega
    · simp [e, b, a]
    · simp [e, b, a, readRegs, hb]
    · intro i hi hi23
      have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
      have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
      simp [e, b, a, readRegs, hi0, hi1, hi23]
  | true =>
    refine ⟨2, by omega, a, ha.seq (.ite_true (by simp [a, hb]) (.base (.skip a))), ?_, ?_, ?_⟩
    · simp [a]
    · simp [a, hb]
    · intro i _ hi
      simp [a, hi]

theorem resetCandidateFlags_eval (d : Data) :
    Eval resetCandidateFlags 2 d
      ⟨Function.update (Function.update d.regs 21 false) 22 true, d.stacks⟩ :=
  .seq (.base (.atom _ _)) (.base (.atom _ _))
theorem testedCandidate_eval (F : Formula) (C : Clause)
    (mask width size threshold : List Bool) (d : Data)
    (h15 : d.stacks 15 = (Filter.clauseCode C).reverse)
    (h16 : d.stacks 16 = width) (h17 : d.stacks 17 = threshold)
    (h18 : d.stacks 18 = Filter.formulaCode F) (h20 : d.stacks 20 = size)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) :
    ∃ t ≤ candidateBound F C mask width size threshold, ∃ e : Data,
      Eval (testedCandidate mask) t d e ∧
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 15 []) 9
          (if accepted F C mask width size threshold then
            Filter.clauseCode (masked mask C) else [])) 12
        (if accepted F C mask width size threshold then
          Filter.formulaCode (selectedFamily F (masked mask C) width) else []) ∧
      e.regs 23 = accepted F C mask width size threshold ∧
      e.regs 21 = false ∧ e.regs 22 = true := by
  obtain ⟨t, ht, a, ha, has, hav, _⟩ := prepareCandidate_eval C mask d h15
    (hwork 5) (hwork 6) (hwork 7) (hwork 8) h9 h10 h11
  rw [h20] at ht hav
  have ha9 : a.stacks 9 = Filter.clauseCode (masked mask C) := by simp [has]
  have ha10 : a.stacks 10 = [] := by simp [has, h10]
  have ha11 : a.stacks 11 = [] := by simp [has, h11]
  have ha12 : a.stacks 12 = [] := by simp [has, h12]
  have ha16 : a.stacks 16 = width := by simp [has, h16]
  have ha17 : a.stacks 17 = threshold := by simp [has, h17]
  have ha18 : a.stacks 18 = Filter.formulaCode F := by simp [has, h18]
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    have hi9 : Fin.castAdd 15 i ≠ (9 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 9 at hh; have := i.isLt; omega
    have hi15 : Fin.castAdd 15 i ≠ (15 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 15 at hh; have := i.isLt; omega
    simpa [has, hi9, hi15] using hwork i
  by_cases hsize : (masked mask C).length = BinaryArithmetic.toNat size
  · have ha4 : a.regs 4 = true := by simpa [hsize] using hav
    obtain ⟨u, hu, b, hb, hbs, hb4, _⟩ := checkCandidate_eval F (masked mask C) width a
      ha9 ha16 ha18 haw ha10 ha11 ha12
    rw [ha17] at hu hb4
    have hb9 : b.stacks 9 = Filter.clauseCode (masked mask C) := by simp [hbs, ha9]
    have hb12 : b.stacks 12 = Filter.formulaCode (selectedFamily F (masked mask C) width) := by
      simp [hbs]
    obtain ⟨v, hv, c, hc, hcs, hc23, _⟩ := retainCandidate_eval b
    let e : Data := ⟨Function.update (Function.update c.regs 21 false) 22 true, c.stacks⟩
    have he := resetCandidateFlags_eval c
    have haccept : b.regs 4 = accepted F C mask width size threshold := by
      simpa [accepted, hsize] using hb4
    refine ⟨t + ((u + v + 1) + 2), ?_, e,
      ha.seq ((Eval.ite_true ha4 (hb.seq hc)).seq he), ?_, ?_, ?_, ?_⟩
    · rw [hb9, hb12] at hv
      unfold candidateBound
      omega
    · change c.stacks = _
      rw [hcs, haccept, hbs, has]
      funext i
      cases hh : accepted F C mask width size threshold <;>
        simp [Function.update_apply]
      split_ifs <;> rfl
    · simp [e, hc23, haccept]
    · simp [e]
    · simp [e]
  · have ha4 : a.regs 4 = false := by simpa [hsize] using hav
    let b : Data := ⟨readRegs a.regs 0 1 none, Function.update a.stacks 9 []⟩
    let c : Data := ⟨Function.update b.regs 23 false, b.stacks⟩
    let e : Data := ⟨Function.update (Function.update c.regs 21 false) 22 true, c.stacks⟩
    have hb := clear_eval 9 a
    have hc : Eval (atom (.set 23 false)) 1 b c := .base (.atom _ _)
    have he := resetCandidateFlags_eval c
    refine ⟨t + ((2 * (a.stacks 9).length + 3 + 1 + 1) + 2), ?_, e,
      ha.seq ((Eval.ite_false ha4 (hb.seq hc)).seq he), ?_, ?_, ?_, ?_⟩
    · rw [ha9]
      unfold candidateBound
      omega
    · simpa [e, c, b, has, accepted, hsize] using h12
    · simp [e, c, accepted, hsize]
    · simp [e]
    · simp [e]

theorem widthFamily_eq (F : Formula) (width : List Bool) :
    widthFamily F width = (F.filter fun C => decide (C.length = BinaryArithmetic.toNat width)).reverse := by
  simp only [widthFamily, Filter.result, ExecCNF.subset, Bool.and_true]

theorem mem_widthFamily (F : Formula) (C : Clause) (width : List Bool) :
    C ∈ widthFamily F width ↔ C ∈ F ∧ C.length = BinaryArithmetic.toNat width := by
  simp [widthFamily_eq]

/-- The two streaming reversals cancel. No family is duplicated in the output. -/
theorem selectedFamily_widthFamily (F : Formula) (H : Clause) (width : List Bool) :
    selectedFamily (widthFamily F width) H width =
      selectedRaw F (BinaryArithmetic.toNat width) H := by
  simp only [selectedFamily, Filter.result, widthFamily_eq, List.filter_reverse,
    List.reverse_reverse, selectedRaw, List.filter_filter]
  congr 1
  funext C
  cases decide (C.length = BinaryArithmetic.toNat width) <;> cases ExecCNF.subset H C <;> rfl
@[simp] theorem update_high_apply_low (store : Fin 24 → List Bool) (port : Fin 24)
    (word : List Bool) (i : Fin 9) (hport : 9 ≤ port.val) :
    Function.update store port word (Fin.castAdd 15 i) = store (Fin.castAdd 15 i) := by
  have hne : Fin.castAdd 15 i ≠ port := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = port.val at hh
    have := i.isLt
    omega
  simp [hne]

theorem familyInit_eval (F : Formula) (width : List Bool) (d : Data)
    (h13 : d.stacks 13 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h16 : d.stacks 16 = []) (h18 : d.stacks 18 = []) :
    ∃ t ≤ familyInitBound F width, ∃ e : Data,
      Eval (familyInit width) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 16 width) 18
        (Filter.formulaCode (widthFamily F width)) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨a, ha, has, har⟩ := load_eval 9 [false] d
  simp only [h9, List.append_nil] at has
  obtain ⟨b, hb, hbs, hbr⟩ := load_eval 16 width a
  have ha16 : a.stacks 16 = [] := by simp [has, h16]
  simp only [ha16, List.append_nil] at hbs
  have hb13 : b.stacks 13 = Filter.formulaCode F := by simp [hbs, has, h13]
  have hb10 : b.stacks 10 = [] := by simp [hbs, has, h10]
  have hb8 : b.stacks 8 = [] := by simpa [hbs, has] using hwork 8
  let c : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 10 (b.stacks 13)⟩
  have hc := copy_eval 13 10 b (by decide) (by decide) (by decide) hb8 hb10
  have hc9 : c.stacks 9 = Filter.clauseCode [] := by simp [c, hbs, has, Filter.clauseCode, Encoding.encodeList]
  have hc16 : c.stacks 16 = width := by simp [c, hbs]
  have hc10 : c.stacks 10 = Filter.formulaCode F := by simp [c, hb13]
  have hcw (i : Fin 9) : c.stacks (Fin.castAdd 15 i) = [] := by
    change Function.update b.stacks 10 (b.stacks 13) (Fin.castAdd 15 i) = []
    rw [update_high_apply_low _ 10 _ i (by decide), hbs,
      update_high_apply_low _ 16 _ i (by decide), has,
      update_high_apply_low _ 9 _ i (by decide)]
    exact hwork i
  obtain ⟨u, hu, e, he, hes, her⟩ := filterCall_eval F [] width c hc9 hc16 hc10 hcw
    (by simpa [c, hbs, has] using h11) (by simpa [c, hbs, has] using h12)
  have he9 : e.stacks 9 = [false] := by simp [hes, hc9, Filter.clauseCode, Encoding.encodeList]
  have he12 : e.stacks 12 = Filter.formulaCode (widthFamily F width) := by simp [hes, widthFamily]
  have he18 : e.stacks 18 = [] := by simp [hes, c, hbs, has, h18]
  have he8 : e.stacks 8 = [] := by simpa [hes, c, hbs, has] using hwork 8
  let f : Data := ⟨readRegs e.regs 0 1 none, Function.update e.stacks 9 []⟩
  have hf := clear_eval 9 e
  have hf8 : f.stacks 8 = [] := by simp [f, he8]
  have hmove := move_eval 12 18 f (by decide) (by decide) (by decide) hf8
  let g : Data := ⟨readRegs (readRegs f.regs 0 1 none) 0 1 none,
    Function.update (Function.update f.stacks 12 []) 18 (f.stacks 12 ++ f.stacks 18)⟩
  refine ⟨(2 * ([false] : List Bool).length + 1) + ((2 * width.length + 1) +
    (7 * (b.stacks 13).length + 5 + (u + (2 * (e.stacks 9).length + 3 +
      (6 * (f.stacks 12).length + 6))))), ?_, g,
    ha.seq (hb.seq (hc.seq (he.seq (hf.seq hmove)))), ?_, ?_⟩
  · simp only [hb13, he9, List.length_singleton] at *
    have hf12 : f.stacks 12 = Filter.formulaCode (widthFamily F width) := by simp [f, he12]
    rw [hf12]
    simp only [Filter.clauseCode, Encoding.length_encodeList_nil] at hu
    have hsum : 1 + (Filter.formulaCode F).length + width.length + 1 =
        (Filter.formulaCode F).length + width.length + 2 := by omega
    rw [hsum] at hu
    unfold familyInitBound
    omega
  · funext i
    fin_cases i <;>
      simp [g, f, hes, c, hbs, has, h9, h10, h12, h18, widthFamily]
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hei := her i hi
    have hbi := hbr i (by omega)
    have hai := har i (by omega)
    simpa [g, f, c, readRegs, hi0, hi1, hbi, hai] using hei
theorem parameterInit_eval (exponent : ℕ) (size base family : List Bool) (d : Data)
    (h19 : d.stacks 19 = base) (h18 : d.stacks 18 = family)
    (h20 : d.stacks 20 = []) (h10 : d.stacks 10 = []) (h17 : d.stacks 17 = [])
    (h14 : d.stacks 14 = []) (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = []) :
    ∃ t ≤ parameterInitBound exponent size base family, ∃ word : List Bool, ∃ e : Data,
      Eval (parameterInit exponent size) t d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 20 size) 17 word) 14 family ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
      word.length ≤ 1 + exponent * base.length ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨a, ha, has, har⟩ := load_eval 20 size d
  simp only [h20, List.append_nil] at has
  have ha19 : a.stacks 19 = base := by simp [has, h19]
  have ha10 : a.stacks 10 = [] := by simp [has, h10]
  have ha17 : a.stacks 17 = [] := by simp [has, h17]
  have haw (i : Fin 6) : a.stacks (Fin.castAdd 18 i) = [] := by
    have hi20 : Fin.castAdd 18 i ≠ (20 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 20 at hh; have := i.isLt; omega
    have hcast : Fin.castAdd 15 (Fin.castAdd 3 i) = Fin.castAdd 18 i := by
      apply Fin.ext
      rfl
    simpa only [has, Function.update_apply, hi20, ite_false, hcast] using
      hwork (Fin.castAdd 3 i)
  obtain ⟨t, ht, word, b, hb, hbs, hv, hl, hbr⟩ := powerCall_eval exponent base a ha19 ha10 ha17 haw
  have hb8 : b.stacks 8 = [] := by simpa [hbs, has] using hwork 8
  have hb14 : b.stacks 14 = [] := by simp [hbs, has, h14]
  have hb18 : b.stacks 18 = family := by simp [hbs, has, h18]
  let e : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 14 (b.stacks 18)⟩
  have he := copy_eval 18 14 b (by decide) (by decide) (by decide) hb8 hb14
  refine ⟨2 * size.length + 1 + (t + (7 * (b.stacks 18).length + 5)), ?_, word, e,
    ha.seq (hb.seq he), ?_, hv, hl, ?_⟩
  · rw [hb18]
    unfold parameterInitBound
    omega
  · simp [e, hbs, has, hb18]
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i hi
    have hai := har i hi
    simp [e, readRegs, hi0, hi1, hbi, hai]
theorem clearMany_eval (ports : List (Fin 24)) (bound : ℕ) (d : Data)
    (hbound : ∀ port ∈ ports, (d.stacks port).length ≤ bound) :
    ∃ t ≤ ports.length * (2 * bound + 3), ∃ e : Data,
      Eval (clearMany ports) t d e ∧ e.stacks = eraseWords ports d.stacks ∧
      (∀ i : Fin 24, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  induction ports generalizing d with
  | nil => exact ⟨0, by simp, d, .base (.skip d), by funext i; simp [eraseWords], fun _ _ _ => rfl⟩
  | cons port rest ih =>
    let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩
    have ha := clear_eval port d
    have hab (p : Fin 24) (hp : p ∈ rest) : (a.stacks p).length ≤ bound := by
      by_cases heq : p = port
      · subst p; simp [a]
      · simpa [a, heq] using hbound p (by simp [hp])
    obtain ⟨t, ht, e, he, hes, her⟩ := ih a hab
    refine ⟨2 * (d.stacks port).length + 3 + t, ?_, e, ha.seq he, ?_, ?_⟩
    · have hp := hbound port (by simp)
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [hes]
      funext i
      by_cases heq : i = port
      · subst i; simp [eraseWords, a]
      · by_cases hi : i ∈ rest <;> simp [eraseWords, a, hi, heq]
    · intro i hi0 hi1
      simpa [a, readRegs, hi0, hi1] using her i hi0 hi1

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread]
  | cons bits rest ih =>
    rw [Encoding.length_encodeList_cons]
    simp only [RecordPrograms.unread, List.append_nil]
    split <;> omega

structure ScanReady (F : Formula) (width size threshold : List Bool) (d : Data) : Prop where
  width_word : d.stacks 16 = width
  size_word : d.stacks 20 = size
  threshold_word : d.stacks 17 = threshold
  family_word : d.stacks 18 = Filter.formulaCode F
  scratch : ∀ i : Fin 13, d.stacks (Fin.castAdd 11 i) = []

def scanTest (F : Formula) (mask width size threshold bits : List Bool) : Bool :=
  match Filter.decodeClause bits with
  | some C => accepted F C mask width size threshold
  | none => false

def scanCost (F : Formula) (mask width size threshold bits : List Bool) : ℕ :=
  match Filter.decodeClause bits with
  | some C => candidateBound F C mask width size threshold
  | none => 0

structure ScanEffect (F : Formula) (mask width size threshold bits : List Bool)
    (before after : Data) : Prop where
  shape : ∃ C ∈ F, bits = Filter.clauseCode C ∧
    after.stacks = Function.update (Function.update before.stacks 9
      (if accepted F C mask width size threshold then Filter.clauseCode (masked mask C) else [])) 12
      (if accepted F C mask width size threshold then
        Filter.formulaCode (selectedFamily F (masked mask C) width) else [])

/-- Failed callbacks restore the empty output banks. A successful callback
retains its actual output, and no further callback is required by the iterator. -/
theorem scan_callback_contract (F : Formula) (mask width size threshold : List Bool)
    (bits tail : List Bool) (base : Data)
    (hbits : ∃ C ∈ F, bits = Filter.clauseCode C)
    (hbase : ScanReady F width size threshold base) :
    ∃ t next, t ≤ scanCost F mask width size threshold bits ∧
      (scanTest F mask width size threshold bits = false → ScanReady F width size threshold next) ∧
      ScanEffect F mask width size threshold bits base next ∧
      Eval (candidate mask) t
        (RecordPrograms.state ports base false true false tail bits.reverse)
        (RecordPrograms.state ports next false true (scanTest F mask width size threshold bits) tail []) := by
  obtain ⟨C, hCF, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Filter.clauseCode C).reverse
  have hwork (i : Fin 9) : d.stacks (Fin.castAdd 15 i) = [] := by
    have hi14 : Fin.castAdd 15 i ≠ (14 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 14 at hh; have := i.isLt; omega
    have hi15 : Fin.castAdd 15 i ≠ (15 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 15 at hh; have := i.isLt; omega
    have hcast : Fin.castAdd 11 (Fin.castAdd 4 i) = Fin.castAdd 15 i := by
      apply Fin.ext
      rfl
    simpa [d, RecordPrograms.state, ports, hi14, hi15, hcast] using
      hbase.scratch (Fin.castAdd 4 i)
  obtain ⟨t, ht, e, he, hes, he23, he21, he22⟩ := testedCandidate_eval F C mask width size threshold d
    (by simp [d, RecordPrograms.state, ports])
    (by simpa [d, RecordPrograms.state, ports] using hbase.width_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.threshold_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.family_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.size_word) hwork
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 9)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 10)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 11)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 12)
  let next : Data := ⟨e.regs, Function.update (Function.update e.stacks 14 (base.stacks 14))
    15 (base.stacks 15)⟩
  have hnext : next.stacks = Function.update (Function.update base.stacks 9
      (if accepted F C mask width size threshold then Filter.clauseCode (masked mask C) else [])) 12
      (if accepted F C mask width size threshold then
        Filter.formulaCode (selectedFamily F (masked mask C) width) else []) := by
    funext i
    simp only [next, hes, d, RecordPrograms.state, ports, Function.update_apply]
    split_ifs <;> simp_all
  have htest : scanTest F mask width size threshold (Filter.clauseCode C) =
      accepted F C mask width size threshold := by simp [scanTest]
  refine ⟨t, next, by simpa [scanCost] using ht, ?_, ⟨C, hCF, rfl, hnext⟩, ?_⟩
  · intro hfalse
    rw [htest] at hfalse
    have hs : next.stacks = base.stacks := by
      rw [hnext, hfalse]
      simp only [Bool.false_eq_true, ite_false]
      funext i
      by_cases hi9 : i = 9
      · subst i; simpa using (hbase.scratch 9).symm
      by_cases hi12 : i = 12
      · subst i; simpa using (hbase.scratch 12).symm
      simp [hi9, hi12]
    exact ⟨by simpa only [hs] using hbase.width_word,
      by simpa only [hs] using hbase.size_word,
      by simpa only [hs] using hbase.threshold_word,
      by simpa only [hs] using hbase.family_word,
      by simpa only [hs] using hbase.scratch⟩
  · have hstate : RecordPrograms.state ports next false true
        (scanTest F mask width size threshold (Filter.clauseCode C)) tail [] = e := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext i
        by_cases hi21 : i = 21
        · subst i; simp [ports, he21]
        by_cases hi22 : i = 22
        · subst i; simp [ports, he22]
        by_cases hi23 : i = 23
        · subst i; simp [ports, htest, he23]
        simp [ports, next, hi21, hi22, hi23]
      · funext i
        simp only [RecordPrograms.state, ports, hnext, hes, d, Function.update_apply]
        split_ifs <;> simp_all
    simpa only [candidate, hstate] using he

theorem scan_eval (F : Formula) (mask width size threshold : List Bool) (base : Data)
    (hbase : ScanReady F width size threshold base) (v p f : Bool) :
    ∃ t next, t ≤ 3 + RecordPrograms.budget (scanCost F mask width size threshold) (Filter.records F) ∧
      ((Filter.records F).any (scanTest F mask width size threshold) = false →
        ScanReady F width size threshold next) ∧
      RecordPrograms.Visits (scanTest F mask width size threshold)
        (ScanEffect F mask width size threshold) (Filter.records F) base next ∧
      Eval (RecordPrograms.iterate ports (candidate mask)) t
        (RecordPrograms.state ports base v p f (Filter.formulaCode F) [])
        (RecordPrograms.state ports next false true
          ((Filter.records F).any (scanTest F mask width size threshold))
          (RecordPrograms.unread (scanTest F mask width size threshold) (Filter.records F) []) []) := by
  have hvalid : ∀ bits ∈ Filter.records F, ∃ C ∈ F, bits = Filter.clauseCode C := by
    intro bits hbits
    obtain ⟨C, hCF, rfl⟩ := List.mem_map.mp hbits
    exact ⟨C, hCF, rfl⟩
  simpa only [← Filter.formulaCode_records, List.append_nil] using
    RecordSearch.iterate_run_with_miss_invariant ports (candidate mask)
      (scanTest F mask width size threshold) (scanCost F mask width size threshold)
      (ScanReady F width size threshold) (ScanEffect F mask width size threshold)
      (fun bits => ∃ C ∈ F, bits = Filter.clauseCode C)
      (scan_callback_contract F mask width size threshold)
      (Filter.records F) [] base hvalid hbase v p f

theorem ScanEffect.frame {F : Formula} {mask width size threshold bits : List Bool}
    {before after : Data} (h : ScanEffect F mask width size threshold bits before after)
    (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : after.stacks i = before.stacks i := by
  obtain ⟨C, _, _, hs⟩ := h.shape
  simp [hs, hi9, hi12]

theorem scan_visits_frame {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : after.stacks i = before.stacks i := by
  induction h with
  | nil base => rfl
  | hit _ he => exact he.frame i hi9 hi12
  | miss _ he _ ih => exact ih.trans (he.frame i hi9 hi12)

theorem scan_visits_hit {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (hfound : records.any (scanTest F mask width size threshold) = true) :
    ∃ C ∈ F, accepted F C mask width size threshold = true ∧
      after.stacks 9 = Filter.clauseCode (masked mask C) ∧
      after.stacks 12 = Filter.formulaCode (selectedFamily F (masked mask C) width) := by
  induction h with
  | nil base => simp at hfound
  | hit ht he =>
    obtain ⟨C, hCF, rfl, hs⟩ := he.shape
    have htrue : accepted F C mask width size threshold = true := by simpa [scanTest] using ht
    exact ⟨C, hCF, htrue, by simp [hs, htrue], by simp [hs, htrue]⟩
  | miss ht _ _ ih => exact ih (by simpa [List.any_cons, ht] using hfound)

theorem scan_visits_miss {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (hfound : records.any (scanTest F mask width size threshold) = false)
    (h9 : before.stacks 9 = []) (h12 : before.stacks 12 = []) :
    after.stacks = before.stacks := by
  induction h with
  | nil base => rfl
  | hit ht _ => simp [List.any_cons, ht] at hfound
  | @miss bits rest base middle next ht he _ ih =>
    obtain ⟨C, _, rfl, hs⟩ := he.shape
    have hfalse : accepted F C mask width size threshold = false := by simpa [scanTest] using ht
    have heq : _ = _ := hs
    rw [hfalse] at heq
    simp only [Bool.false_eq_true, ite_false] at heq
    have h9update : Function.update base.stacks 9 [] = base.stacks := by
      rw [← h9, Function.update_eq_self]
    have h12update : Function.update base.stacks 12 [] = base.stacks := by
      rw [← h12, Function.update_eq_self]
    rw [h9update, h12update] at heq
    exact (ih (by simpa [List.any_cons, ht] using hfound)
      (by simpa only [heq] using h9) (by simpa only [heq] using h12)).trans heq

theorem scan_any_eq (F : Formula) (mask width size threshold : List Bool) :
    (Filter.records F).any (scanTest F mask width size threshold) =
      F.any (fun C => accepted F C mask width size threshold) := by
  simp [Filter.records, List.any_map, Function.comp_def, scanTest]

theorem clauseCode_masked_length_le (mask : List Bool) (C : Clause) :
    (Filter.clauseCode (masked mask C)).length ≤ (Filter.clauseCode C).length :=
  EncodingLength.length_le_of_sublist id (masked_sublist mask C)

theorem formulaCode_selectedFamily_length_le (F : Formula) (H : Clause) (width : List Bool) :
    (Filter.formulaCode (selectedFamily F H width)).length ≤ (Filter.formulaCode F).length := by
  unfold selectedFamily Filter.formulaCode
  rw [EncodingLength.length_reverse]
  exact EncodingLength.length_le_of_sublist Filter.clauseCode List.filter_sublist

theorem clauseCode_member_length_le (F : Formula) (C : Clause) (h : C ∈ F) :
    (Filter.clauseCode C).length ≤ (Filter.formulaCode F).length := by
  have hh := Filter.member_length_le (Filter.records F) (Filter.clauseCode C)
    (List.mem_map.mpr ⟨C, h, rfl⟩)
  simpa only [← Filter.formulaCode_records] using hh

def scanVolume (F : Formula) (mask width size threshold : List Bool) : ℕ :=
  2 * (Filter.formulaCode F).length + mask.length + width.length + size.length + threshold.length + 1

theorem candidateBound_le (F : Formula) (C : Clause) (mask width size threshold : List Bool)
    (hC : C ∈ F) :
    candidateBound F C mask width size threshold ≤ 2000 * scanVolume F mask width size threshold ^ 3 := by
  let L := scanVolume F mask width size threshold
  have hCsize := clauseCode_member_length_le F C hC
  have hHsize := clauseCode_masked_length_le mask C
  have hSsize := formulaCode_selectedFamily_length_le F (masked mask C) width
  have hL : 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hH : (Filter.clauseCode (masked mask C)).length + size.length + 1 ≤ L := by
    dsimp [L, scanVolume]; omega
  have hF : (Filter.clauseCode (masked mask C)).length + (Filter.formulaCode F).length +
      width.length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hS : (Filter.formulaCode (selectedFamily F (masked mask C) width)).length +
      threshold.length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hHpow := Nat.pow_le_pow_left hH 2
  have hFpow := Nat.pow_le_pow_left hF 3
  have hSpow := Nat.pow_le_pow_left hS 2
  have hsq : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by decide)
  have hlin : L ≤ L ^ 3 := Nat.le_self_pow (by decide) L
  have hsmall : (Filter.formulaCode F).length + mask.length + 1 ≤ L := by
    dsimp [L, scanVolume]; omega
  unfold candidateBound prepareCandidateBound checkCandidateBound CoreMaskProgram.runtimeBound
  change _ ≤ 2000 * L ^ 3
  dsimp only [Filter.clauseCode] at *
  omega

theorem scan_budget_le (F : Formula) (mask width size threshold : List Bool) :
    3 + RecordPrograms.budget (scanCost F mask width size threshold) (Filter.records F) ≤
      3000 * scanVolume F mask width size threshold ^ 4 := by
  let L := scanVolume F mask width size threshold
  have hcost (bits : List Bool) (hbits : bits ∈ Filter.records F) :
      scanCost F mask width size threshold bits ≤ 0 * bits.length + 2000 * L ^ 3 := by
    obtain ⟨C, hCF, rfl⟩ := List.mem_map.mp hbits
    simpa only [scanCost, Filter.decodeClause_clauseCode, Nat.zero_mul, Nat.zero_add] using
      candidateBound_le F C mask width size threshold hCF
  have hb := RecordPrograms.program_budget_le_input
    (scanCost F mask width size threshold) (Filter.records F) 0 (2000 * L ^ 3) hcost
  have hcode : ProgramEncoding.encodeRecords (Filter.records F) = Filter.formulaCode F := by
    exact (Filter.formulaCode_records F).symm
  rw [hcode] at hb
  simp only [Nat.zero_add] at hb
  have hL : 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hlen : (Filter.formulaCode F).length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hmul := Nat.mul_le_mul_left (2000 * L ^ 3 + 17) hlen
  have hlin : L ≤ L ^ 4 := Nat.le_self_pow (by decide) L
  have heq : (2000 * L ^ 3 + 17) * L = 2000 * L ^ 4 + 17 * L := by ring
  rw [heq] at hmul
  change _ ≤ 3000 * L ^ 4
  omega

structure Boundary (F : Formula) (base : List Bool) (d : Data) : Prop where
  formula_word : d.stacks 13 = Filter.formulaCode F
  parameter_word : d.stacks 19 = base
  scratch : ∀ i : Fin 24, i ≠ 13 → i ≠ 19 → d.stacks i = []

def phaseVolume (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) : ℕ :=
  2 * (Filter.formulaCode (widthFamily F c.bits)).length + mask.length + c.bits.length +
    h.bits.length + (1 + (c - h) * base.length) + 1

def phaseBound (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) : ℕ :=
  familyInitBound F c.bits +
    parameterInitBound (c - h) h.bits base (Filter.formulaCode (widthFamily F c.bits)) +
    3000 * phaseVolume F base c h mask ^ 4 + 5 * (2 * phaseVolume F base c h mask + 3)

theorem phase_eval (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool)
    (d : Data) (hd : Boundary F base d) :
    ∃ word : List Bool, ∃ t ≤ phaseBound F base c h mask, ∃ e : Data,
      Eval (phase c h mask) t d e ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ (c - h) ∧
      word.length ≤ 1 + (c - h) * base.length ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = (widthFamily F c.bits).any
        (fun C => accepted (widthFamily F c.bits) C mask c.bits h.bits word) ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → ∃ C ∈ widthFamily F c.bits,
        accepted (widthFamily F c.bits) C mask c.bits h.bits word = true ∧
        e.stacks 9 = Filter.clauseCode (masked mask C) ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c (masked mask C))) := by
  let Fc := widthFamily F c.bits
  have hw (i : Fin 9) : d.stacks (Fin.castAdd 15 i) = [] := by
    apply hd.scratch
    · intro heq; have hh := congrArg Fin.val heq; change i.val = 13 at hh; have := i.isLt; omega
    · intro heq; have hh := congrArg Fin.val heq; change i.val = 19 at hh; have := i.isLt; omega
  obtain ⟨u, hu, a, ha, has, _⟩ := familyInit_eval F c.bits d hd.formula_word hw
    (hd.scratch 9 (by decide) (by decide)) (hd.scratch 10 (by decide) (by decide))
    (hd.scratch 11 (by decide) (by decide)) (hd.scratch 12 (by decide) (by decide))
    (hd.scratch 16 (by decide) (by decide)) (hd.scratch 18 (by decide) (by decide))
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    rw [has, update_high_apply_low _ 18 _ i (by decide),
      update_high_apply_low _ 16 _ i (by decide)]
    exact hw i
  obtain ⟨v, hv, word, b, hb, hbs, hval, hlen, _⟩ := parameterInit_eval (c - h) h.bits base
    (Filter.formulaCode Fc) a
    (by simp [has, hd.parameter_word]) (by simp [has, Fc])
    (by simpa [has] using hd.scratch 20 (by decide) (by decide))
    (by simpa [has] using hd.scratch 10 (by decide) (by decide))
    (by simpa [has] using hd.scratch 17 (by decide) (by decide))
    (by simpa [has] using hd.scratch 14 (by decide) (by decide)) haw
  have hready : ScanReady Fc c.bits h.bits word b := by
    constructor
    · simp [hbs, has]
    · simp [hbs]
    · simp [hbs]
    · simp [hbs, has, Fc]
    · intro i
      have hi14 : Fin.castAdd 11 i ≠ (14 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 14 at hh; have := i.isLt; omega
      have hi17 : Fin.castAdd 11 i ≠ (17 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 17 at hh; have := i.isLt; omega
      have hi20 : Fin.castAdd 11 i ≠ (20 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 20 at hh; have := i.isLt; omega
      have hi18 : Fin.castAdd 11 i ≠ (18 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 18 at hh; have := i.isLt; omega
      have hi16 : Fin.castAdd 11 i ≠ (16 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 16 at hh; have := i.isLt; omega
      have hi13 : Fin.castAdd 11 i ≠ (13 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 13 at hh; have := i.isLt; omega
      have hi19 : Fin.castAdd 11 i ≠ (19 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 19 at hh; have := i.isLt; omega
      simpa [hbs, has, hi14, hi17, hi20, hi18, hi16] using hd.scratch _ hi13 hi19
  obtain ⟨w, next, hwtime, hmiss, hvisits, hscan⟩ := scan_eval Fc mask c.bits h.bits word b
    hready (b.regs 21) (b.regs 22) (b.regs 23)
  have hstart : RecordPrograms.state ports b (b.regs 21) (b.regs 22) (b.regs 23)
      (Filter.formulaCode Fc) [] = b := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simp [ports, hbs]
    · simpa [ports, hbs, has] using hd.scratch 15 (by decide) (by decide)
  rw [hstart] at hscan
  let test := scanTest Fc mask c.bits h.bits word
  let found := (Filter.records Fc).any test
  let z := RecordPrograms.state ports next false true found
    (RecordPrograms.unread test (Filter.records Fc) []) []
  change Eval (RecordPrograms.iterate ports (candidate mask)) w b z at hscan
  have hframe := scan_visits_frame hvisits
  let L := phaseVolume F base c h mask
  have hvolume : scanVolume Fc mask c.bits h.bits word ≤ L := by
    dsimp [scanVolume, L, phaseVolume, Fc]
    omega
  have hwbound : w ≤ 3000 * L ^ 4 :=
    hwtime.trans ((scan_budget_le Fc mask c.bits h.bits word).trans
      (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left hvolume 4)))
  have hzbound (i : Fin 24) (hi : i ∈ ([14, 18, 16, 20, 17] : List (Fin 24))) :
      (z.stacks i).length ≤ L := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have hh := unread_length_le test (Filter.records Fc)
      rw [← Filter.formulaCode_records] at hh
      change (RecordPrograms.unread test (Filter.records Fc) []).length ≤ L
      dsimp [L, phaseVolume, Fc] at *
      omega
    all_goals simp only [z, RecordPrograms.state, ports, Function.update_apply]
    all_goals rw [hframe _ (by decide) (by decide)]
    all_goals simp only [hbs, has, Function.update_apply]
    all_goals norm_num
    all_goals dsimp [L, phaseVolume, Fc] at *; omega
  obtain ⟨x, hx, e, he, hes, her⟩ := clearMany_eval [14, 18, 16, 20, 17] L z hzbound
  have hef (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : e.stacks i = d.stacks i := by
    rw [hes]
    by_cases hi : i ∈ ([14, 18, 16, 20, 17] : List (Fin 24))
    · simp only [eraseWords, hi, ite_true]
      symm
      apply hd.scratch
      · intro h; subst i; simp at hi
      · intro h; subst i; simp at hi
    · have hi14 : i ≠ 14 := by intro h; subst i; simp at hi
      have hi18 : i ≠ 18 := by intro h; subst i; simp at hi
      have hi16 : i ≠ 16 := by intro h; subst i; simp at hi
      have hi20 : i ≠ 20 := by intro h; subst i; simp at hi
      have hi17 : i ≠ 17 := by intro h; subst i; simp at hi
      by_cases hi15 : i = 15
      · subst i
        simpa [eraseWords, z, RecordPrograms.state, ports] using
          (hd.scratch 15 (by decide) (by decide)).symm
      · simp only [eraseWords, hi, ite_false, z, RecordPrograms.state, ports,
          Function.update_apply, hi14, hi15, ite_false]
        rw [hframe i hi9 hi12]
        simp [hbs, has, hi14, hi18, hi16, hi20, hi17]
  have he9 : e.stacks 9 = next.stacks 9 := by simp [hes, eraseWords, z, RecordPrograms.state, ports]
  have he12 : e.stacks 12 = next.stacks 12 := by simp [hes, eraseWords, z, RecordPrograms.state, ports]
  have he23 : e.regs 23 = found := by
    simpa [z, RecordPrograms.state, ports] using her 23 (by decide) (by decide)
  refine ⟨word, u + (v + (w + x)), ?_, e, ha.seq (hb.seq (hscan.seq he)),
    hval, hlen, hef, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil] at hx
    unfold phaseBound
    dsimp [Fc] at hv
    dsimp [L] at hwbound hx
    omega
  · exact he23.trans (scan_any_eq Fc mask c.bits h.bits word)
  · intro hfalse
    have hn := scan_visits_miss hvisits (he23.symm.trans hfalse)
      (hready.scratch 9) (hready.scratch 12)
    funext i
    by_cases hi9 : i = 9
    · subst i; rw [he9, hn]; simp [hbs, has]
    by_cases hi12 : i = 12
    · subst i; rw [he12, hn]; simp [hbs, has]
    exact hef i hi9 hi12
  · intro htrue
    obtain ⟨C, hCF, hacc, h9, h12⟩ := scan_visits_hit hvisits (he23.symm.trans htrue)
    refine ⟨C, hCF, hacc, he9.trans h9, ?_⟩
    simpa only [ArithmeticExpressionSupport.bits_value] using
      he12.trans (h12.trans (congrArg Filter.formulaCode (selectedFamily_widthFamily F (masked mask C) c.bits)))

def passCandidate (F : Formula) (M : ℕ) (p : ℕ × ℕ × List Bool) (C : Clause) : Bool :=
  decide ((masked p.2.2 C).length = p.2.1) &&
    decide (M ^ (p.1 - p.2.1) ≤ (selectedRaw F p.1 (masked p.2.2 C)).length)

def passFound (F : Formula) (M : ℕ) (p : ℕ × ℕ × List Bool) : Bool :=
  (widthFamily F p.1.bits).any (passCandidate F M p)

theorem accepted_eq_passCandidate (F : Formula) (base word : List Bool) (c h : ℕ)
    (mask : List Bool) (hword : BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ (c - h))
    (C : Clause) :
    accepted (widthFamily F c.bits) C mask c.bits h.bits word =
      passCandidate F (BinaryArithmetic.toNat base) (c, h, mask) C := by
  have hcount := congrArg List.length (selectedFamily_widthFamily F (masked mask C) c.bits)
  simp only [selectedFamily, List.length_reverse, ArithmeticExpressionSupport.bits_value] at hcount
  simp only [accepted, ArithmeticExpressionSupport.bits_value, hword, hcount, passCandidate]

theorem phase_eval_natural (F : Formula) (base : List Bool) (p : ℕ × ℕ × List Bool)
    (d : Data) (hd : Boundary F base d) :
    ∃ t ≤ phaseBound F base p.1 p.2.1 p.2.2, ∃ e : Data,
      Eval (phase p.1 p.2.1 p.2.2) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = passFound F (BinaryArithmetic.toNat base) p ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → ∃ C ∈ widthFamily F p.1.bits,
        passCandidate F (BinaryArithmetic.toNat base) p C = true ∧
        e.stacks 9 = Filter.clauseCode (masked p.2.2 C) ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F p.1 (masked p.2.2 C))) := by
  obtain ⟨word, t, ht, e, he, hval, _, hframe, hfound, hmiss, hhit⟩ :=
    phase_eval F base p.1 p.2.1 p.2.2 d hd
  have hh (C : Clause) := accepted_eq_passCandidate F base word p.1 p.2.1 p.2.2 hval C
  refine ⟨t, ht, e, he, hframe, ?_, hmiss, ?_⟩
  · simpa only [hh, passFound] using hfound
  · intro htrue
    obtain ⟨C, hC, hacc, hs9, hs12⟩ := hhit htrue
    exact ⟨C, hC, (hh C).symm.trans hacc, hs9, hs12⟩

inductive SearchHit (F : Formula) (M : ℕ) (ps : List (ℕ × ℕ × List Bool)) (e : Data) : Prop
  | intro (before : List (ℕ × ℕ × List Bool)) (chosen : ℕ × ℕ × List Bool)
      (after : List (ℕ × ℕ × List Bool)) (clause : Clause)
      (split : ps = before ++ chosen :: after)
      (failed : ∀ p ∈ before, passFound F M p = false)
      (clause_mem : clause ∈ widthFamily F chosen.1.bits)
      (accepted : passCandidate F M chosen clause = true)
      (core_word : e.stacks 9 = Filter.clauseCode (masked chosen.2.2 clause))
      (family_word : e.stacks 12 = Filter.formulaCode (selectedRaw F chosen.1 (masked chosen.2.2 clause))) :
      SearchHit F M ps e

def chainBudget (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool)) : ℕ :=
  (ps.map fun p => phaseBound F base p.1 p.2.1 p.2.2).sum + 2 * ps.length

theorem chain_stop (commands : List Code) (d : Data) (hfound : d.regs 23 = true) :
    ∃ t ≤ 1, Eval (chain commands) t d d := by
  cases commands with
  | nil => exact ⟨0, by decide, .base (.skip d)⟩
  | cons head tail => exact ⟨1, by decide, .ite_true hfound (.base (.skip d))⟩

theorem chain_eval (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool))
    (d : Data) (hd : Boundary F base d) (hfalse : d.regs 23 = false) :
    ∃ t ≤ chainBudget F base ps, ∃ e : Data,
      Eval (chain (ps.map fun p => phase p.1 p.2.1 p.2.2)) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = ps.any (passFound F (BinaryArithmetic.toNat base)) ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → SearchHit F (BinaryArithmetic.toNat base) ps e) := by
  induction ps generalizing d with
  | nil =>
    refine ⟨0, by simp [chainBudget], d, .base (.skip d), fun _ _ _ => rfl, ?_,
      fun _ => rfl, ?_⟩
    · simpa using hfalse
    · intro hh; simp [hfalse] at hh
  | cons p ps ih =>
    obtain ⟨u, hu, a, ha, haframe, hafound, hamiss, hahit⟩ := phase_eval_natural F base p d hd
    cases hh : a.regs 23 with
    | false =>
      have has := hamiss hh
      have haBoundary : Boundary F base a := by
        constructor
        · simpa only [has] using hd.formula_word
        · simpa only [has] using hd.parameter_word
        · simpa only [has] using hd.scratch
      obtain ⟨v, hv, e, he, heframe, hefound, hemiss, hehit⟩ := ih a haBoundary hh
      refine ⟨u + v + 1, ?_, e, Eval.ite_false hfalse (ha.seq he), ?_, ?_, ?_, ?_⟩
      · simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · intro i hi9 hi12
        exact (heframe i hi9 hi12).trans (haframe i hi9 hi12)
      · simp only [List.any_cons, ← hafound, hh, Bool.false_or]
        exact hefound
      · intro hf
        exact (hemiss hf).trans has
      · intro ht
        obtain ⟨before, chosen, after, C, hsplit, hfailed, hC, hacc, h9, h12⟩ := hehit ht
        refine ⟨p :: before, chosen, after, C, ?_, ?_, hC, hacc, h9, h12⟩
        · simp only [List.cons_append, hsplit]
        · intro q hq
          rcases List.mem_cons.mp hq with heq | hrest
          · subst q; exact hafound.symm.trans hh
          · exact hfailed q hrest
    | true =>
      obtain ⟨v, hv, he⟩ := chain_stop (ps.map fun p => phase p.1 p.2.1 p.2.2) a hh
      obtain ⟨C, hC, hacc, h9, h12⟩ := hahit hh
      refine ⟨u + v + 1, ?_, a, Eval.ite_false hfalse (ha.seq he), haframe, ?_, ?_, ?_⟩
      · simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons]
        omega
      · simp [List.any_cons, ← hafound, hh]
      · intro hf; simp [hh] at hf
      · intro _
        exact ⟨[], p, ps, C, rfl, by simp, hC, hacc, h9, h12⟩

theorem rawCandidate_witness {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, ∃ mask, mask.length = k ∧ C.length = c ∧ masked mask C = H := by
  obtain ⟨C, hCF, hC⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, hm, heq⟩ := List.mem_map.mp hC
  obtain ⟨hc, hH⟩ := Prod.mk.inj heq
  exact ⟨C, hCF, mask, (mem_masks mask k).mp hm, hc, hH⟩

theorem rawCandidate_failure (k : ℕ) (F : Formula) (M c : ℕ) (H : Clause)
    (hraw : (c, H) ∈ rawCandidates k F)
    (hfail : ∀ mask, mask.length = k → passFound F M (c, H.length, mask) = false) :
    (selectedRaw F c H).length < M ^ (c - H.length) := by
  obtain ⟨C, hCF, mask, hm, hc, hH⟩ := rawCandidate_witness k F c H hraw
  have hmem : C ∈ widthFamily F c.bits := by
    rw [mem_widthFamily]
    simpa only [ArithmeticExpressionSupport.bits_value] using And.intro hCF hc
  have hn := List.any_eq_false.mp (hfail mask hm) C hmem
  simpa [passCandidate, hH, Nat.not_le] using hn

theorem SearchHit.priority (k : ℕ) (F : Formula) (M : ℕ) (e : Data)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hit : SearchHit F M (passes k) e) :
    ∃ c H, RawPriority k F M c H ∧ e.stacks 9 = Filter.clauseCode H ∧
      e.stacks 12 = Filter.formulaCode (selectedRaw F c H) := by
  obtain ⟨before, ⟨c, h, mask⟩, after, C, hsplit, hfailed, hC, hacc, h9, h12⟩ := hit
  have hp : (c, h, mask) ∈ passes k := by rw [hsplit]; simp
  obtain ⟨hc2, hck, hhpos, hhproper, hmask⟩ := (mem_passes k c h mask).mp hp
  have hCF : C ∈ F ∧ C.length = c := by
    simpa only [mem_widthFamily, ArithmeticExpressionSupport.bits_value] using hC
  have hparts : (masked mask C).length = h ∧
      M ^ (c - h) ≤ (selectedRaw F c (masked mask C)).length := by
    simpa only [passCandidate, Bool.and_eq_true, decide_eq_true_eq] using hacc
  refine ⟨c, masked mask C, ?_, h9, h12⟩
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨C, hCF.1, List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hmask, ?_⟩⟩
    simp [hCF.2]
  · omega
  · omega
  · simpa only [hparts.1] using hparts.2
  · intro d core hraw hpos hproper hdc
    have hdwidth : d ≤ k := by
      obtain ⟨D, hD, hlen, _⟩ := rawCandidate_spec k F d core hraw
      rw [← hlen]
      exact hwidth D hD
    apply rawCandidate_failure k F M d core hraw
    intro other hother
    have hpm : (d, core.length, other) ∈ passes k :=
      (mem_passes k d core.length other).mpr ⟨by omega, hdwidth, hpos, hproper, hother⟩
    exact hfailed _ (higher_priority_mem_before hsplit hpm (Or.inl hdc))
  · intro core hraw hlarge hproper
    apply rawCandidate_failure k F M c core hraw
    intro other hother
    have hpm : (c, core.length, other) ∈ passes k :=
      (mem_passes k c core.length other).mpr ⟨hc2, hck, by omega, hproper, hother⟩
    exact hfailed _ (higher_priority_mem_before hsplit hpm (Or.inr ⟨rfl, by change h < core.length; omega⟩))

theorem passes_failure (k : ℕ) (F : Formula) (M : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hfail : (passes k).any (passFound F M) = false)
    (c : ℕ) (H : Clause) (hraw : (c, H) ∈ rawCandidates k F)
    (hpos : 0 < H.length) (hproper : H.length < c) :
    (selectedRaw F c H).length < M ^ (c - H.length) := by
  have hcwidth : c ≤ k := by
    obtain ⟨C, hC, hc, _⟩ := rawCandidate_spec k F c H hraw
    rw [← hc]
    exact hwidth C hC
  apply rawCandidate_failure k F M c H hraw
  intro mask hmask
  have hm : (c, H.length, mask) ∈ passes k :=
    (mem_passes k c H.length mask).mpr ⟨by omega, hcwidth, hpos, hproper, hmask⟩
  simpa only [Bool.not_eq_true] using List.any_eq_false.mp hfail _ hm

theorem command_eval (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ 1 + chainBudget F base (passes k), ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode H ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c H)) := by
  let a : Data := ⟨Function.update d.regs 23 false, d.stacks⟩
  have ha : Eval (atom (.set 23 false)) 1 d a := .base (.atom _ _)
  obtain ⟨t, ht, e, he, hframe, hfound, hmiss, hhit⟩ := chain_eval F base (passes k) a
      ⟨hd.formula_word, hd.parameter_word, hd.scratch⟩ (by simp [a])
  refine ⟨1 + t, by omega, e, ha.seq he, hframe, ?_, ?_⟩
  · intro hf
    refine ⟨hmiss hf, ?_⟩
    exact passes_failure k F (BinaryArithmetic.toNat base) hwidth (hfound.symm.trans hf)
  · intro hf
    exact (hhit hf).priority k F (BinaryArithmetic.toNat base) e hwidth

theorem rawCandidate_map {α β : Type*} (f : α → β) (k : ℕ) (F : List (List α))
    (c : ℕ) (H : List α) (hraw : (c, H) ∈ rawCandidates k F) :
    (c, H.map f) ∈ rawCandidates k (F.map (List.map f)) := by
  obtain ⟨C, hCF, mask, hm, hc, hH⟩ := rawCandidate_witness k F c H hraw
  apply List.mem_flatMap.mpr
  refine ⟨C.map f, List.mem_map.mpr ⟨C, hCF, rfl⟩,
    List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hm, ?_⟩⟩
  simp [List.length_map, hc, masked_map, hH]

theorem rawPriority_of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (k : ℕ) (F : List (List α)) (M c : ℕ)
    (word : List β) (priority : RawPriority k (F.map (List.map f)) M c word) :
    ∃ H : List α, H.map f = word ∧ RawPriority k F M c H := by
  obtain ⟨Cword, hCF, mask, hm, hc, hH⟩ :=
    rawCandidate_witness k (F.map (List.map f)) c word priority.candidate
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hCF
  let H := masked mask C
  have hmap : H.map f = word := by simpa only [masked_map] using hH
  have hlen : H.length = word.length := by rw [← hmap, List.length_map]
  have hclen : C.length = c := by simpa only [List.length_map] using hc
  refine ⟨H, hmap, ?_⟩
  constructor
  · apply List.mem_flatMap.mpr
    exact ⟨C, hC, List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hm, by simp [hclen, H]⟩⟩
  · simpa only [hlen] using priority.core_nonempty
  · simpa only [hlen] using priority.core_proper
  · have ht := priority.threshold
    rw [← hmap, List.length_map, selectedRaw_map f hf, List.length_map] at ht
    exact ht
  · intro d core hraw hpos hproper hdc
    have hh := priority.minimum d (core.map f) (rawCandidate_map f k F d core hraw)
      (by simpa only [List.length_map] using hpos)
      (by simpa only [List.length_map] using hproper) hdc
    simpa only [List.length_map, selectedRaw_map f hf] using hh
  · intro core hraw hlarge hproper
    have hh := priority.maximum (core.map f) (rawCandidate_map f k F c core hraw)
      (by simpa only [List.length_map, ← hlen] using hlarge)
      (by simpa only [List.length_map] using hproper)
    simpa only [List.length_map, selectedRaw_map f hf] using hh

def inputVolume (F : Formula) (base : List Bool) : ℕ :=
  (Filter.formulaCode F).length + base.length + 1

def powerCoefficient (exponent : ℕ) : ℕ :=
  100 * (exponent + 1) ^ 2 + 20 * (exponent + 1) * (exponent.bits.length + 1) + 6

def phaseScale (c h : ℕ) (mask : List Bool) : ℕ :=
  2 + mask.length + c.bits.length + h.bits.length + (c - h) + 2

def phaseCoefficient (c h : ℕ) (mask : List Bool) : ℕ :=
  1000 * (c.bits.length + 2) ^ 3 + (powerCoefficient (c - h) + 2 * h.bits.length + 14) +
    3000 * phaseScale c h mask ^ 4 + (10 * phaseScale c h mask + 15)

theorem widthFamily_code_length_le (F : Formula) (width : List Bool) :
    (Filter.formulaCode (widthFamily F width)).length ≤ (Filter.formulaCode F).length :=
  formulaCode_selectedFamily_length_le F [] width

theorem familyInitBound_le (F : Formula) (width : List Bool) :
    familyInitBound F width ≤ 1000 * ((Filter.formulaCode F).length + width.length + 2) ^ 3 := by
  let L := (Filter.formulaCode F).length + width.length + 2
  have hf := widthFamily_code_length_le F width
  have hlin : L ≤ L ^ 3 := Nat.le_self_pow (by decide) L
  have hL : 1 ≤ L ^ 3 := by apply one_le_pow₀; dsimp [L]; omega
  change _ ≤ 1000 * L ^ 3
  unfold familyInitBound
  change 3 + (2 * width.length + 1) + (7 * (Filter.formulaCode F).length + 5) +
    (600 * L ^ 3 + 3) + 5 + (6 * (Filter.formulaCode (widthFamily F width)).length + 6) ≤ _
  have hF : (Filter.formulaCode F).length ≤ L := by dsimp [L]; omega
  have hW : width.length ≤ L := by dsimp [L]; omega
  have hF3 := hF.trans hlin
  have hW3 := hW.trans hlin
  omega

theorem parameterInitBound_le (F : Formula) (base size : List Bool) (c exponent : ℕ) :
    parameterInitBound exponent size base (Filter.formulaCode (widthFamily F c.bits)) ≤
      (powerCoefficient exponent + 2 * size.length + 14) * inputVolume F base ^ 2 := by
  let V := inputVolume F base
  have hp := ThresholdPower.runtime_polynomial exponent base
  change PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3 ≤
    powerCoefficient exponent * (base.length + 1) ^ 2 at hp
  have hb : base.length + 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hp' := hp.trans (Nat.mul_le_mul_left (powerCoefficient exponent) (Nat.pow_le_pow_left hb 2))
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hV2 : 1 ≤ V ^ 2 := one_le_pow₀ hV
  have hlin : V ≤ V ^ 2 := Nat.le_self_pow (by decide) V
  have hf := widthFamily_code_length_le F c.bits
  have hfamily : (Filter.formulaCode (widthFamily F c.bits)).length ≤ V ^ 2 := by
    have hF : (Filter.formulaCode F).length ≤ V := by dsimp [V, inputVolume]; omega
    exact hf.trans (hF.trans hlin)
  have hconst := Nat.mul_le_mul_left (2 * size.length + 7) hV2
  unfold parameterInitBound
  change _ ≤ (powerCoefficient exponent + 2 * size.length + 14) * V ^ 2
  nlinarith only [hp', hfamily, hconst]

theorem phaseVolume_le (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) :
    phaseVolume F base c h mask ≤ phaseScale c h mask * inputVolume F base := by
  let V := inputVolume F base
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hF : (Filter.formulaCode F).length ≤ V := by dsimp [V, inputVolume]; omega
  have hb : base.length ≤ V := by dsimp [V, inputVolume]; omega
  have hf := widthFamily_code_length_le F c.bits
  have hprod := Nat.mul_le_mul_left (c - h) hb
  have hc := Nat.mul_le_mul_left (mask.length + c.bits.length + h.bits.length + 2) hV
  unfold phaseVolume phaseScale
  change _ ≤ (2 + mask.length + c.bits.length + h.bits.length + (c - h) + 2) * V
  nlinarith only [hF, hf, hprod, hc]

theorem phaseBound_polynomial (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) :
    phaseBound F base c h mask ≤ phaseCoefficient c h mask * inputVolume F base ^ 4 := by
  let V := inputVolume F base
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hV4 : 1 ≤ V ^ 4 := one_le_pow₀ hV
  have hlin : V ≤ V ^ 4 := Nat.le_self_pow (by decide) V
  have hsq : V ^ 2 ≤ V ^ 4 := pow_le_pow_right₀ hV (by decide)
  have hcube : V ^ 3 ≤ V ^ 4 := pow_le_pow_right₀ hV (by decide)
  have hsize : (Filter.formulaCode F).length + c.bits.length + 2 ≤ (c.bits.length + 2) * V := by
    have hvf : (Filter.formulaCode F).length + 1 ≤ V := by dsimp [V, inputVolume]; omega
    have hh := Nat.mul_le_mul_left (c.bits.length + 1) hV
    nlinarith only [hvf, hh]
  have hf := (familyInitBound_le F c.bits).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hsize 3))
  rw [mul_pow, ← Nat.mul_assoc] at hf
  have hf' := hf.trans (Nat.mul_le_mul_left (1000 * (c.bits.length + 2) ^ 3) hcube)
  have hp := (parameterInitBound_le F base h.bits c (c - h)).trans
    (Nat.mul_le_mul_left (powerCoefficient (c - h) + 2 * h.bits.length + 14) hsq)
  have hv := phaseVolume_le F base c h mask
  have hv4 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left hv 4)
  rw [mul_pow, ← Nat.mul_assoc] at hv4
  have hclean := Nat.mul_le_mul_left (10 * phaseScale c h mask) hlin
  have hconst := Nat.mul_le_mul_left 15 hV4
  unfold phaseBound phaseCoefficient
  change _ ≤ (1000 * (c.bits.length + 2) ^ 3 +
    (powerCoefficient (c - h) + 2 * h.bits.length + 14) +
    3000 * phaseScale c h mask ^ 4 + (10 * phaseScale c h mask + 15)) * V ^ 4
  nlinarith only [hf', hp, hv4, hv, hclean, hconst]

def selectorCoefficient (k : ℕ) : ℕ :=
  1 + ((passes k).map fun p => phaseCoefficient p.1 p.2.1 p.2.2).sum + 2 * (passes k).length

theorem chainBudget_polynomial (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool)) :
    chainBudget F base ps ≤
      ((ps.map fun p => phaseCoefficient p.1 p.2.1 p.2.2).sum + 2 * ps.length) *
        inputVolume F base ^ 4 := by
  have hV : 1 ≤ inputVolume F base ^ 4 := by
    apply one_le_pow₀
    unfold inputVolume
    omega
  induction ps with
  | nil => simp [chainBudget]
  | cons p ps ih =>
    have hp := phaseBound_polynomial F base p.1 p.2.1 p.2.2
    simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith only [ih, hp, hV]

theorem commandBound_polynomial (k : ℕ) (F : Formula) (base : List Bool) :
    1 + chainBudget F base (passes k) ≤ selectorCoefficient k * inputVolume F base ^ 4 := by
  have hc := chainBudget_polynomial F base (passes k)
  have hV : 1 ≤ inputVolume F base ^ 4 := by
    apply one_le_pow₀
    unfold inputVolume
    omega
  unfold selectorCoefficient
  nlinarith only [hc, hV]

theorem Boundary.stack_length_le (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (i : Fin 24) : (d.stacks i).length ≤ inputVolume F base := by
  by_cases hi13 : i = 13
  · subst i; rw [hd.formula_word]; unfold inputVolume; omega
  by_cases hi19 : i = 19
  · subst i; rw [hd.parameter_word]; unfold inputVolume; omega
  rw [hd.scratch i hi13 hi19]
  simp

theorem Boundary.dataBits_le (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) {l : ℕ} (pc : Option (Fin l)) :
    dataBits (d.withPC pc) ≤ 24 * inputVolume F base := by
  unfold dataBits
  calc
    _ ≤ ∑ _ : Fin 24, inputVolume F base := by
      apply Finset.sum_le_sum
      intro i _
      exact hd.stack_length_le F base d i
    _ = _ := by simp

theorem command_execution (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ selectorCoefficient k * inputVolume F base ^ 4, ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode H ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c H)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (program k) prefixSteps (d.withPC (some (program k).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          (selectorCoefficient k + 24) * inputVolume F base ^ 4) := by
  obtain ⟨t, ht, e, he, hframe, hmiss, hhit⟩ := command_eval k F base d hd hwidth
  have ht' := ht.trans (commandBound_polynomial k F base)
  refine ⟨t, ht', e, he, hframe, hmiss, hhit, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have hl := StructuredSpace.local_stack_bound (program k)
    (steps := t) (hd.dataBits_le F base d (some (program k).entry))
    prefixSteps intermediate hprefix htrace i
  have hV : inputVolume F base ≤ inputVolume F base ^ 4 := Nat.le_self_pow (by decide) _
  nlinarith only [hl, ht', hV]

theorem command_execution_map {α : Type*} [DecidableEq α]
    (f : α → List Bool) (hf : Function.Injective f) (k : ℕ) (F : List (List α))
    (base : List Bool) (d : Data)
    (hd : Boundary (F.map (List.map f)) base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ selectorCoefficient k * inputVolume (F.map (List.map f)) base ^ 4, ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode (H.map f) ∧
        e.stacks 12 = Filter.formulaCode ((selectedRaw F c H).map (List.map f))) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (program k) prefixSteps (d.withPC (some (program k).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          (selectorCoefficient k + 24) * inputVolume (F.map (List.map f)) base ^ 4) := by
  have hw : ∀ C ∈ F.map (List.map f), C.length ≤ k := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    simpa only [List.length_map] using hwidth D hD
  obtain ⟨t, ht, e, he, hframe, hmiss, hhit, hspace⟩ :=
    command_execution k (F.map (List.map f)) base d hd hw
  refine ⟨t, ht, e, he, hframe, ?_, ?_, hspace⟩
  · intro hfalse
    obtain ⟨hs, hfails⟩ := hmiss hfalse
    refine ⟨hs, ?_⟩
    intro c H hraw hpos hproper
    have hh := hfails c (H.map f) (rawCandidate_map f k F c H hraw)
      (by simpa only [List.length_map] using hpos)
      (by simpa only [List.length_map] using hproper)
    simpa only [selectedRaw_map f hf, List.length_map] using hh
  · intro htrue
    obtain ⟨c, word, hpriority, h9, h12⟩ := hhit htrue
    obtain ⟨H, hH, hpriority'⟩ := rawPriority_of_map f hf k F (BinaryArithmetic.toNat base) c word hpriority
    refine ⟨c, H, hpriority', ?_, ?_⟩
    · simpa only [hH] using h9
    · simpa only [← hH, selectedRaw_map f hf] using h12

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
