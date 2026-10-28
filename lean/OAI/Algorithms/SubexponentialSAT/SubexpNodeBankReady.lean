import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankStage

namespace OAI.Algorithms

/-!
# Concrete readiness and full frame for the node bank stage

The hypotheses identify the actual matrix bundle and the four protected
scalar words. They imply the native mapper input after the stage's four
physical copies. The final stack equation includes the gap between the two
mapped workspace blocks as well as all protected scalar ports.
-/

namespace SubexponentialSAT.SubexpNodeBankReady

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeBasisStage (Data copied)
open SubexpNodeBankStage (ports moves workspace frame Input finished budget program)

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

/-- Concrete producer facts, before the four scalar copies. Registers and
all stacks outside the native workspace are otherwise arbitrary. -/
structure Ready {p rows : ℕ} [Fact p.Prime]
    (d : Data) (matrices : List (SubexpNodeBankMap.Matrix p rows)) : Prop where
  temporary : d.stacks 0 = []
  source : d.stacks 201 = Encoding.encodeList SubexpNodeBankMap.payload matrices
  modulus : d.stacks 279 = Subexp.MatrixWordEncoding.modulus p
  zeroWord : d.stacks 277 = Subexp.MatrixWordEncoding.zero p
  tokens : d.stacks 280 =
    ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.tokens p)
  rowCount : d.stacks 264 = List.replicate rows true
  work : ∀ i : Fin 64, i.val < 44 → i ≠ 32 → d.stacks (ports i) = []

private theorem copied_frame (d : Data) (i : Fin 288) (hi : i ∉ workspace) :
    (copied moves d).stacks i = d.stacks i := by
  apply SubexpNodeBasisStage.copied_frame
  intro m hm
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    intro he
    exact hi (by simp [workspace, he])

private theorem port_not_workspace (i : Fin 64)
    (hi : i.val < 40 ∨ 44 ≤ i.val) : ports i ∉ workspace := by
  intro hm
  simp only [workspace, List.mem_cons, List.mem_nil_iff, or_false] at hm
  have hex : ∃ j : Fin 64, 40 ≤ j.val ∧ j.val < 44 ∧ ports j = ports i := by
    rcases hm with h | h | h | h
    · exact ⟨40, by decide, by decide, h.symm⟩
    · exact ⟨41, by decide, by decide, h.symm⟩
    · exact ⟨42, by decide, by decide, h.symm⟩
    · exact ⟨43, by decide, by decide, h.symm⟩
  obtain ⟨j, hj0, hj1, he⟩ := hex
  have hji := SubexpNodeBankStage.ports_injective he
  subst j
  omega

private theorem copied_common {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) :
    (copied moves d).stacks 209 = Subexp.MatrixWordEncoding.modulus p ∧
    (copied moves d).stacks 210 = Subexp.MatrixWordEncoding.zero p ∧
    (copied moves d).stacks 211 =
      ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.tokens p) ∧
    (copied moves d).stacks 212 = List.replicate rows true := by
  have h209 : d.stacks 209 = [] := h.work 40 (by decide) (by decide)
  have h210 : d.stacks 210 = [] := h.work 41 (by decide) (by decide)
  have h211 : d.stacks 211 = [] := h.work 42 (by decide) (by decide)
  have h212 : d.stacks 212 = [] := h.work 43 (by decide) (by decide)
  simp [moves, copied, afterCopy, StackRoutines.copyStacks,
    h209, h210, h211, h212, h.modulus, h.zeroWord, h.tokens, h.rowCount]

private theorem input_below40 {p rows : ℕ} [Fact p.Prime]
    (matrices : List (SubexpNodeBankMap.Matrix p rows))
    (regs : Fin 16 → Bool) (fr : Fin 20 → List Bool) (i : Fin 64)
    (hi : i.val < 40) :
    (SubexpNodeBankMap.input matrices regs fr).stacks i =
      if i = 32 then Encoding.encodeList SubexpNodeBankMap.payload matrices else [] := by
  fin_cases i <;>
    norm_num [SubexpNodeBankMap.input, SubexpNodeBankMap.store,
      Fin.ext_iff, Fin.castLT] at hi
  all_goals norm_num [SubexpNodeBankMap.input, SubexpNodeBankMap.store,
    Fin.ext_iff, Fin.castLT]

private theorem input_frame {p rows : ℕ} [Fact p.Prime]
    (matrices : List (SubexpNodeBankMap.Matrix p rows))
    (regs : Fin 16 → Bool) (fr : Fin 20 → List Bool) (i : Fin 20) :
    (SubexpNodeBankMap.input matrices regs fr).stacks (Fin.natAdd 44 i) = fr i := by
  have hi : Fin.natAdd 44 i = Fin.natAdd 32 (Fin.natAdd 8 (Fin.natAdd 4 i)) := by
    apply Fin.ext
    change 44 + i.val = 32 + (8 + (4 + i.val))
    omega
  rw [hi]
  simp only [SubexpNodeBankMap.input, SubexpNodeBankMap.store,
    SubexpNodeBankMap.common, Fin.addCases_right]

/-- The four real copies establish the exact native input state. -/
theorem ready_input {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) : Input d matrices := by
  unfold Input
  apply state_ext
  · rfl
  · funext i
    change (copied moves d).stacks (ports i) =
      (SubexpNodeBankMap.input matrices (copied moves d).regs (frame d)).stacks i
    refine Fin.addCases (m := 40) (n := 24) (fun j => ?_) (fun j => ?_) i
    · have hj : (Fin.castAdd 24 j).val < 40 := j.isLt
      rw [copied_frame d _ (port_not_workspace _ (Or.inl hj)),
        input_below40 _ _ _ _ hj]
      by_cases he : Fin.castAdd 24 j = (32 : Fin 64)
      · rw [he, ite_eq_left rfl]
        exact h.source
      · rw [ite_eq_right he]
        exact h.work _ (by omega) he
    · refine Fin.addCases (m := 4) (n := 20) (fun q => ?_) (fun q => ?_) j
      · obtain ⟨h0,h1,h2,h3⟩ := copied_common h
        fin_cases q
        · exact h0
        · exact h1
        · exact h2
        · exact h3
      · have he : Fin.natAdd 40 (Fin.natAdd 4 q) = Fin.natAdd 44 q := by
          apply Fin.ext
          change 40 + (4 + q.val) = 44 + q.val
          omega
        rw [he, input_frame]
        exact copied_frame d _ (port_not_workspace _ (Or.inr (by
          change 44 ≤ 44 + q.val
          omega)))

/-- The fixed stage executes from the concrete producer facts, with its
existing budget including copies, the native mapper, cleanup, and halt. -/
theorem program_runs_ready {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) :
    ∃ rf : Fin 16 → Bool, RunsIn program (budget d matrices + 1)
      (d.withPC (some program.entry)) ((finished d matrices rf).withPC none) :=
  SubexpNodeBankStage.program_runs d matrices h.temporary (ready_input h)

private theorem result_below40 {p rows : ℕ} [Fact p.Prime]
    (matrices : List (SubexpNodeBankMap.Matrix p rows))
    (regs : Fin 16 → Bool) (fr : Fin 20 → List Bool) (i : Fin 64)
    (hi : i.val < 40) :
    (SubexpNodeBankMap.result matrices regs fr).stacks i =
      if i = 35 then ProgramEncoding.encodeRecords
        (matrices.map SubexpNodeBankMap.bankList) else [] := by
  fin_cases i <;>
    norm_num [SubexpNodeBankMap.result, SubexpNodeBankMap.store,
      Fin.ext_iff, Fin.castLT] at hi
  all_goals norm_num [SubexpNodeBankMap.result, SubexpNodeBankMap.store,
    Fin.ext_iff, Fin.castLT]

private theorem native_result_frame {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) (rf : Fin 16 → Bool) (i : Fin 64)
    (h32 : i ≠ 32) (h35 : i ≠ 35) (hi : i.val < 40 ∨ 44 ≤ i.val) :
    (SubexpNodeBankMap.result matrices rf (frame d)).stacks i = d.stacks (ports i) := by
  rcases hi with hi | hi
  · rw [result_below40 _ _ _ _ hi, ite_eq_right h35, h.work i (by omega) h32]
  · let j : Fin 20 := ⟨i.val - 44, by omega⟩
    have he : i = Fin.natAdd 44 j := by
      apply Fin.ext
      change i.val = 44 + (i.val - 44)
      omega
    rw [he, SubexpNodeBankMap.result_frame]
    rfl

/-- Every stack other than the consumed source and produced output is
restored, including temporary scalar copies and the unmapped gap. -/
theorem finished_frame {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) (rf : Fin 16 → Bool) (i : Fin 288)
    (h201 : i ≠ 201) (h204 : i ≠ 204) :
    (finished d matrices rf).stacks i = d.stacks i := by
  by_cases hw : i ∈ workspace
  · rw [SubexpNodeBankStage.finished_workspace_empty _ _ _ _ hw]
    simp only [workspace, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (h.work 40 (by decide) (by decide)).symm
    · exact (h.work 41 (by decide) (by decide)).symm
    · exact (h.work 42 (by decide) (by decide)).symm
    · exact (h.work 43 (by decide) (by decide)).symm
  · rw [finished, SubexpNodeBankStage.cleared_frame _ _ _ hw]
    unfold SubexpNodeBankStage.mapped
    by_cases hp : ∃ j, ports j = i
    · obtain ⟨j, rfl⟩ := hp
      rw [embedState_stack _ _ _ _ SubexpNodeBankStage.ports_injective]
      apply native_result_frame h rf j
      · intro he
        exact h201 (by simp only [he, SubexpNodeBankStage.ports_input])
      · intro he
        exact h204 (by simp only [he, SubexpNodeBankStage.ports_output])
      · by_contra hn
        have hj0 : 40 ≤ j.val := by omega
        have hj1 : j.val < 44 := by omega
        have hj : j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 := by omega
        rcases hj with rfl | rfl | rfl | rfl <;> exact hw (by decide)
    · rw [embedState_stack_frame _ _ _ _ _ hp]
      exact copied_frame d i hw

/-- Exact stack effect of the complete stage: only ports201 and204 change. -/
theorem finished_stacks {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) (rf : Fin 16 → Bool) :
    (finished d matrices rf).stacks =
      Function.update (Function.update d.stacks 201 []) 204
        (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList)) := by
  funext i
  by_cases h201 : i = 201
  · subst i
    simp only [SubexpNodeBankStage.finished_source_empty,
      Function.update_of_ne (by decide : (201 : Fin 288) ≠ 204), Function.update_self]
  · by_cases h204 : i = 204
    · subst i
      simp only [SubexpNodeBankStage.finished_output, Function.update_self]
    · rw [finished_frame h rf i h201 h204]
      simp [h201, h204]

theorem finished_temporary {p rows : ℕ} [Fact p.Prime]
    {d : Data} {matrices : List (SubexpNodeBankMap.Matrix p rows)}
    (h : Ready d matrices) (rf : Fin 16 → Bool) :
    (finished d matrices rf).stacks 0 = [] :=
  (finished_frame h rf 0 (by decide) (by decide)).trans h.temporary

end SubexponentialSAT.SubexpNodeBankReady

end OAI.Algorithms
