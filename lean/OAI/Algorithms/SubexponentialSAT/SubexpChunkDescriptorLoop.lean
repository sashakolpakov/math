import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorEncoding

namespace OAI.Algorithms

/-! Closed chunk iteration using the concrete unary splitter and byte emitter. -/

namespace SubexponentialSAT.SubexpChunkDescriptorLoop

open BitProgram StructuredProgram StructuredCalls
open SubexpChunkDescriptorProgram SubexpChunkDescriptorEncoding

abbrev copyWidth : StructuredCalls.Cmd 3 10 := .call (StackRoutines.copyProgram 1 2 3 0 1)
abbrev copyIndex : StructuredCalls.Cmd 3 10 := .call (StackRoutines.copyProgram 4 2 3 0 1)

theorem copyWidth_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    StructuredCalls.Eval copyWidth (7 * width.length + 5)
      (work regs remaining width [] index ws ss)
      (work (readRegs regs 0 1 none) remaining width width index ws ss) := by
  have h : StructuredCalls.Eval copyWidth (7 * width.length + 5)
      (work regs remaining width [] index ws ss)
      ⟨readRegs regs 0 1 none,
        StackRoutines.copyStacks 1 2 (work regs remaining width [] index ws ss).stacks⟩ :=
    StructuredCalls.Eval.call _ (ListRegisterProgram.copy_run
    (1 : Fin 10) 2 3 (0 : Fin 3) 1 (by decide) (by decide) (by decide) (by decide)
    regs (work regs remaining width [] index ws ss).stacks rfl)
  convert h using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [work, StackRoutines.copyStacks]

theorem copyIndex_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    StructuredCalls.Eval copyIndex (7 * index.length + 5)
      (work regs remaining width [] index ws ss)
      (work (readRegs regs 0 1 none) remaining width index index ws ss) := by
  have h : StructuredCalls.Eval copyIndex (7 * index.length + 5)
      (work regs remaining width [] index ws ss)
      ⟨readRegs regs 0 1 none,
        StackRoutines.copyStacks 4 2 (work regs remaining width [] index ws ss).stacks⟩ :=
    StructuredCalls.Eval.call _ (ListRegisterProgram.copy_run
    (4 : Fin 10) 2 3 (0 : Fin 3) 1 (by decide) (by decide) (by decide) (by decide)
    regs (work regs remaining width [] index ws ss).stacks rfl)
  convert h using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [work, StackRoutines.copyStacks]

abbrev repeatScope : StructuredCalls.Cmd 3 10 :=
  UnaryForPrograms.forCmd counterPorts (emitBits 6 [true, true, true, true])

theorem repeatScope_visits (counter : List Bool) :
    ∀ (regs : Regs) (remaining width index ws ss : List Bool),
      ∃ costs regs', UnaryForPrograms.Visits counterPorts
        (emitBits 6 [true, true, true, true]) costs (10 * counter.length + 2)
        (work regs remaining width counter index ws ss)
        (work regs' remaining width [] index ws
          (List.replicate (4 * counter.length) true ++ ss)) := by
  induction counter with
  | nil =>
      intro regs remaining width index ws ss
      refine ⟨[], readRegs regs 0 1 none, ?_⟩
      simpa [popped_work] using
        (UnaryForPrograms.Visits.done (p := counterPorts)
          (body := emitBits 6 [true, true, true, true])
          (work regs remaining width [] index ws ss) rfl)
  | cons bit counter ih =>
      intro regs remaining width index ws ss
      let r₁ := readRegs regs 0 1 (some bit)
      obtain ⟨r₂, hb⟩ := emitBits_work6 [true, true, true, true] r₁ remaining width counter index ws ss
      obtain ⟨costs, r₃, ht⟩ := ih r₂ remaining width index ws
        (true :: true :: true :: true :: ss)
      refine ⟨8 :: costs, r₃, ?_⟩
      have hv := UnaryForPrograms.Visits.step
        (p := counterPorts) (body := emitBits 6 [true, true, true, true])
        (d := work regs remaining width (bit :: counter) index ws ss)
        (by simp [work, counterPorts]) (by simpa [popped_work, r₁] using hb)
        (by simp [UnaryForPrograms.popped, work, counterPorts]) ht
      convert hv using 1
      · simp only [List.length_cons]
        omega
      · simp [Nat.mul_add, List.replicate_add, List.append_assoc]

theorem repeatScope_eval (regs : Regs) (remaining width counter index ws ss : List Bool) :
    ∃ regs', StructuredCalls.Eval repeatScope (10 * counter.length + 2)
      (work regs remaining width counter index ws ss)
      (work regs' remaining width [] index ws
        (List.replicate (4 * counter.length) true ++ ss)) := by
  obtain ⟨costs, regs', hv⟩ := repeatScope_visits counter regs remaining width index ws ss
  exact ⟨regs', hv.eval⟩

abbrev emitWidth : StructuredCalls.Cmd 3 10 :=
  .seq (emitBits 5 [true]) (.seq copyWidth (.seq takeChunk (emitBits 5 [false])))

theorem emitWidth_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    ∃ n regs', StructuredCalls.Eval emitWidth n (work regs remaining width [] index ws ss)
      (work regs' (remaining.drop width.length) width [] index
        ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws) ss) ∧
      n ≤ 15 * width.length + 11 := by
  obtain ⟨r₁, h₁⟩ := emitBits_work5 [true] regs remaining width [] index ws ss
  have h₂ := copyWidth_eval r₁ remaining width index (true :: ws) ss
  obtain ⟨n, r₃, h₃, hn⟩ := takeChunk_eval (readRegs r₁ 0 1 none)
    remaining width width index (true :: ws) ss
  obtain ⟨r₄, h₄⟩ := emitBits_work5 [false] r₃ (remaining.drop width.length) width [] index
    (List.replicate (2 * min width.length remaining.length) true ++ true :: ws) ss
  refine ⟨2 + ((7 * width.length + 5) + (n + 2)), r₄, ?_, by omega⟩
  simpa [emitWidth, width_record, List.reverse_append, List.append_assoc] using
    h₁.seq (h₂.seq (h₃.seq h₄))

abbrev emitScope : StructuredCalls.Cmd 3 10 :=
  .seq (emitBits 6 [true, true, true])
    (.seq copyIndex (.seq repeatScope (emitBits 6 scopeSuffix)))

theorem emitScope_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    ∃ regs', StructuredCalls.Eval emitScope (17 * index.length + 31)
      (work regs remaining width [] index ws ss)
      (work regs' remaining width [] index ws
        ((record (Encoding.encodeList Encoding.encodeNat [index.length])).reverse ++ ss)) := by
  obtain ⟨r₁, h₁⟩ := emitBits_work6 [true, true, true] regs remaining width [] index ws ss
  have h₂ := copyIndex_eval r₁ remaining width index ws (true :: true :: true :: ss)
  obtain ⟨r₃, h₃⟩ := repeatScope_eval (readRegs r₁ 0 1 none) remaining width index index ws
    (true :: true :: true :: ss)
  obtain ⟨r₄, h₄⟩ := emitBits_work6 scopeSuffix r₃ remaining width [] index ws
    (List.replicate (4 * index.length) true ++ true :: true :: true :: ss)
  refine ⟨r₄, ?_⟩
  have he := h₁.seq (h₂.seq (h₃.seq h₄))
  convert he using 1
  · dsimp [scopeSuffix]
    omega
  · simp [scope_record, List.reverse_append, List.append_assoc, scopeSuffix]

abbrev incrementIndex : StructuredCalls.Cmd 3 10 := emit 4 true

theorem incrementIndex_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    StructuredCalls.Eval incrementIndex 2 (work regs remaining width [] index ws ss)
      (work (Function.update regs 2 true) remaining width [] (true :: index) ws ss) := by
  have he := emit_eval 4 true (work regs remaining width [] index ws ss)
  convert he using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [work, emitted]

abbrev testRemaining : StructuredCalls.Cmd 3 10 := .base (.atom (.peek 0 0 1))

theorem testRemaining_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    StructuredCalls.Eval testRemaining 1 (work regs remaining width [] index ws ss)
      (work (readRegs regs 0 1 remaining.head?) remaining width [] index ws ss) :=
  .base (.atom _ _)

abbrev chunk : StructuredCalls.Cmd 3 10 :=
  .seq emitWidth (.seq emitScope (.seq incrementIndex testRemaining))

theorem chunk_eval (regs : Regs) (remaining width index ws ss : List Bool) :
    ∃ n regs', StructuredCalls.Eval chunk n (work regs remaining width [] index ws ss)
      (work regs' (remaining.drop width.length) width [] (true :: index)
        ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws)
        ((record (Encoding.encodeList Encoding.encodeNat [index.length])).reverse ++ ss)) ∧
      regs' 1 = (remaining.drop width.length).head?.isSome ∧
      n ≤ 15 * width.length + 17 * index.length + 45 := by
  obtain ⟨n, r₁, h₁, hn⟩ := emitWidth_eval regs remaining width index ws ss
  obtain ⟨r₂, h₂⟩ := emitScope_eval r₁ (remaining.drop width.length) width index
    ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws) ss
  have h₃ := incrementIndex_eval r₂ (remaining.drop width.length) width index
    ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws)
    ((record (Encoding.encodeList Encoding.encodeNat [index.length])).reverse ++ ss)
  have h₄ := testRemaining_eval (Function.update r₂ 2 true) (remaining.drop width.length) width
    (true :: index)
    ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws)
    ((record (Encoding.encodeList Encoding.encodeNat [index.length])).reverse ++ ss)
  exact ⟨n + ((17 * index.length + 31) + (2 + 1)), _, h₁.seq (h₂.seq (h₃.seq h₄)),
    by simp [readRegs], by omega⟩

abbrev loop : StructuredCalls.Cmd 3 10 := .while 1 chunk

def loopBound (ell start count : ℕ) : ℕ :=
  count * (15 * ell + 17 * (start + count) + 46) + 1

theorem loop_eval_aux (n : ℕ) :
    ∀ (remaining : List Bool), remaining.length = n →
      ∀ (regs : Regs) (width index ws ss : List Bool), 0 < width.length →
        regs 1 = remaining.head?.isSome →
        ∃ steps regs', StructuredCalls.Eval loop steps (work regs remaining width [] index ws ss)
          (work regs' [] width []
            (List.replicate (ChunkPartition.count remaining.length width.length) true ++ index)
            ((widthPrefix remaining.length width.length).reverse ++ ws)
            ((scopePrefix index.length (ChunkPartition.count remaining.length width.length)).reverse ++ ss)) ∧
          steps ≤ loopBound width.length index.length
            (ChunkPartition.count remaining.length width.length) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro remaining hlen regs width index ws ss hw hr
      by_cases he : remaining = []
      · subst remaining
        refine ⟨1, regs, ?_, ?_⟩
        · simpa [ChunkPartition.count_zero hw, widthPrefix_zero hw] using
            (StructuredCalls.Eval.while_false (test := (1 : Fin 3)) (body := chunk)
              (a := work regs [] width [] index ws ss) (by simpa [work] using hr))
        · simp [ChunkPartition.count_zero hw, loopBound]
      · have hn : 0 < remaining.length := List.length_pos_iff.mpr he
        obtain ⟨nb, r₁, hb, hflag, hnb⟩ := chunk_eval regs remaining width index ws ss
        have hlt : (remaining.drop width.length).length < n := by
          rw [List.length_drop]
          omega
        obtain ⟨nt, r₂, ht, hnt⟩ := ih (remaining.drop width.length).length hlt
          (remaining.drop width.length) rfl r₁ width (true :: index)
          ((record (List.replicate (min width.length remaining.length) true)).reverse ++ ws)
          ((record (Encoding.encodeList Encoding.encodeNat [index.length])).reverse ++ ss)
          hw hflag
        have hg : (work regs remaining width [] index ws ss).regs 1 = true := by
          change regs 1 = true
          rw [hr]
          cases remaining <;> simp_all
        have hcount := count_step hn hw
        refine ⟨nb + nt + 1, r₂, ?_, ?_⟩
        · have hrun := StructuredCalls.Eval.while_true hg hb ht
          simpa [loop, List.length_drop, hcount, widthPrefix_step hn hw,
            scopePrefix_step, List.reverse_append, List.replicate_succ',
            List.append_assoc] using hrun
        · simp only [List.length_drop, List.length_cons, loopBound] at hnt
          rw [hcount]
          dsimp [loopBound]
          nlinarith

theorem loop_eval (regs : Regs) (remaining width index ws ss : List Bool)
    (hw : 0 < width.length) (hr : regs 1 = remaining.head?.isSome) :
    ∃ steps regs', StructuredCalls.Eval loop steps (work regs remaining width [] index ws ss)
      (work regs' [] width []
        (List.replicate (ChunkPartition.count remaining.length width.length) true ++ index)
        ((widthPrefix remaining.length width.length).reverse ++ ws)
        ((scopePrefix index.length (ChunkPartition.count remaining.length width.length)).reverse ++ ss)) ∧
      steps ≤ loopBound width.length index.length
        (ChunkPartition.count remaining.length width.length) :=
  loop_eval_aux remaining.length remaining rfl regs width index ws ss hw hr

abbrev scan : StructuredCalls.Cmd 3 10 := .seq testRemaining loop

theorem scan_eval (regs : Regs) (remaining width : List Bool) (hw : 0 < width.length) :
    ∃ steps regs', StructuredCalls.Eval scan steps (work regs remaining width [] [] [] [])
      (work regs' [] width []
        (List.replicate (ChunkPartition.count remaining.length width.length) true)
        (widthPrefix remaining.length width.length).reverse
        (scopePrefix 0 (ChunkPartition.count remaining.length width.length)).reverse) ∧
      steps ≤ loopBound width.length 0 (ChunkPartition.count remaining.length width.length) + 1 := by
  obtain ⟨n, regs', he, hn⟩ := loop_eval (readRegs regs 0 1 remaining.head?)
    remaining width [] [] [] hw (by simp [readRegs])
  refine ⟨1 + n, regs', ?_, ?_⟩
  · simpa [scan] using (testRemaining_eval regs remaining width [] [] []).seq he
  · simpa [Nat.add_comm] using Nat.add_le_add_left hn 1

end SubexponentialSAT.SubexpChunkDescriptorLoop

end OAI.Algorithms
