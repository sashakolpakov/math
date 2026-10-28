import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : State R S) (source : State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_register reg stack frame source hreg i).trans (hr i).symm
    · exact (embedState_register_frame reg stack frame source j hj).trans (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack reg stack frame source hstack i).trans (hs i).symm
    · exact (embedState_stack_frame reg stack frame source j hj).trans (hfs j hj).symm

def afterCopy {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval {r s : ℕ} (d : State r s) (src dst tmp : Fin s) (v p : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : v ≠ p)
    (htmp : d.stacks tmp = []) :
    Eval (.call (StackRoutines.copyProgram src dst tmp v p))
      (7 * (d.stacks src).length + 5) d (afterCopy d src dst v p) := by
  apply Eval.call
  have ht := StackRoutines.copyProgram_trace src dst tmp v p hsd hst htd hvp
    d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  simpa [afterCopy, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

def afterTransfer {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r)
    (hsd : src ≠ dst) (hvp : v ≠ p) :
    Eval (.call (StackRoutines.transferProgram src dst v p))
      (3 * (d.stacks src).length + 3) d (afterTransfer d src dst v p) := by
  apply Eval.call
  have ht := StackRoutines.transferProgram_trace src dst v p hsd hvp d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  simpa [afterTransfer, StackRoutines.transferResult, StructuredProgram.State.withPC,
    StackRoutines.transferProgram, Nat.add_assoc] using hh

def afterReverse {r s : ℕ} (d : State r s) (src : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.reverseStacks src d.stacks⟩

theorem reverse_eval {r s : ℕ} (d : State r s) (src tmp₁ tmp₂ : Fin s) (v p : Fin r)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂) (hvp : v ≠ p)
    (ht₁ : d.stacks tmp₁ = []) (ht₂ : d.stacks tmp₂ = []) :
    Eval (.call (StackRoutines.reverseProgram src tmp₁ tmp₂ v p))
      (9 * (d.stacks src).length + 7) d (afterReverse d src v p) := by
  apply Eval.call
  have ht := StackRoutines.reverseProgram_trace src tmp₁ tmp₂ v p h₁ h₂ h₁₂ hvp
    d.regs d.stacks ht₁ ht₂
  have hh := StackRoutines.halt_after_trace _ ht 9 rfl rfl
  simpa [afterReverse, StackRoutines.reverseResult, StructuredProgram.State.withPC,
    StackRoutines.reverseProgram, Nat.add_assoc] using hh

def afterCounted {r s : ℕ} (d : State r s) (counter src dst : Fin s) (v p : Fin r)
    (bits rest : List Bool) : State r s :=
  ⟨readRegs d.regs v p none,
    ArrayPrograms.countedTransferStacks counter src dst bits rest d.stacks⟩

theorem counted_eval {r s : ℕ} (d : State r s) (counter src dst : Fin s) (v p : Fin r)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst) (hvp : v ≠ p)
    (bits rest count : List Bool) (hsrc : d.stacks src = bits ++ rest)
    (hc : d.stacks counter = count) (hlen : count.length = bits.length) :
    Eval (.call (ArrayPrograms.countedTransferProgram counter src dst v p))
      (4 * bits.length + 3) d (afterCounted d counter src dst v p bits rest) := by
  apply Eval.call
  have ht := ArrayPrograms.countedTransferProgram_trace counter src dst v p
    hcs hcd hsd hvp bits rest count d.regs d.stacks hsrc hc hlen
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  simpa [afterCounted, ArrayPrograms.countedTransferResult, StructuredProgram.State.withPC,
    ArrayPrograms.countedTransferProgram, Nat.add_assoc] using hh

/-- Copy the runtime width, consume exactly that many source bits, and restore
their order in the destination. The control table does not contain the width. -/
abbrev takeWord {r s : ℕ} (width counter tmp src dst : Fin s) (v p : Fin r) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram width counter tmp v p))
    (.seq (.call (ArrayPrograms.countedTransferProgram counter src tmp v p))
      (.call (StackRoutines.transferProgram tmp dst v p)))

def afterTake {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r)
    (bits rest : List Bool) : State r s :=
  ⟨readRegs d.regs v p none,
    Function.update (Function.update d.stacks src rest) dst (bits ++ d.stacks dst)⟩

theorem takeWord_eval {r s : ℕ} (d : State r s)
    (width counter tmp src dst : Fin s) (v p : Fin r)
    (distinct : Function.Injective (![width, counter, tmp, src, dst] : Fin 5 → Fin s))
    (hvp : v ≠ p) (bits rest : List Bool)
    (hsrc : d.stacks src = bits ++ rest)
    (hc : d.stacks counter = []) (ht : d.stacks tmp = [])
    (hlen : (d.stacks width).length = bits.length) :
    Eval (takeWord width counter tmp src dst v p) (14 * bits.length + 11)
      d (afterTake d src dst v p bits rest) := by
  have hwc : width ≠ counter := distinct.ne (by decide : (0 : Fin 5) ≠ 1)
  have hwt : width ≠ tmp := distinct.ne (by decide : (0 : Fin 5) ≠ 2)
  have htc : tmp ≠ counter := distinct.ne (by decide : (2 : Fin 5) ≠ 1)
  have hcs : counter ≠ src := distinct.ne (by decide : (1 : Fin 5) ≠ 3)
  have hst : src ≠ tmp := distinct.ne (by decide : (3 : Fin 5) ≠ 2)
  have htd : tmp ≠ dst := distinct.ne (by decide : (2 : Fin 5) ≠ 4)
  have hcd : counter ≠ dst := distinct.ne (by decide : (1 : Fin 5) ≠ 4)
  have hsd : src ≠ dst := distinct.ne (by decide : (3 : Fin 5) ≠ 4)
  have h₁ := copy_eval d width counter tmp v p hwc hwt htc hvp ht
  let d₁ := afterCopy d width counter v p
  have h₂ := counted_eval d₁ counter src tmp v p hcs htc.symm hst hvp bits rest
    (d.stacks width) (by simp [d₁,afterCopy,StackRoutines.copyStacks,hcs.symm,hsrc])
    (by simp [d₁,afterCopy,StackRoutines.copyStacks,hc]) hlen
  let d₂ := afterCounted d₁ counter src tmp v p bits rest
  have h₃ := transfer_eval d₂ tmp dst v p htd hvp
  have hfinal : afterTransfer d₂ tmp dst v p = afterTake d src dst v p bits rest := by
    apply state_ext
    · simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,StackRoutines.readRegs_reset]
    · funext j
      by_cases hd : j = dst
      · subst j
        simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
          StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
          StackRoutines.copyStacks,ht,htd.symm,hcd.symm,htc,hsd.symm]
      · by_cases hjt : j = tmp
        · subst j
          simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
            StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
            StackRoutines.copyStacks,hd,hst.symm,ht]
        · by_cases hjs : j = src
          · subst j
            simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
              StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
              StackRoutines.copyStacks,hd,hjt]
          · by_cases hjc : j = counter
            · subst j
              simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
                StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
                StackRoutines.copyStacks,hd,hjt,hjs,hc]
            · simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
                StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
                StackRoutines.copyStacks,hd,hjt,hjs,hjc]
  have hlen₂ : (d₂.stacks tmp).length = bits.length := by
    simp [d₂,d₁,afterCounted,afterCopy,ArrayPrograms.countedTransferStacks,
      StackRoutines.copyStacks,ht,htc]
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  rw [hfinal] at h
  simpa only [hlen,hlen₂,show 7*bits.length+5+(4*bits.length+3+(3*bits.length+3))=
    14*bits.length+11 by omega,takeWord] using h

/-- Push four zero bits for each item of the runtime counter. -/
abbrev zeroFillProgram {r s : ℕ} (counter dst : Fin s) (v p : Fin r) : Program r s 8 where
  inputStack := counter
  outputStack := dst
  entry := 0
  code := ![.pop counter v p 1,.branch p 2 7,.set v false 3,
    .push dst v 4,.push dst v 5,.push dst v 6,.push dst v 0,.halt]

def zeroFillStacks {s : ℕ} (counter dst : Fin s) (n : ℕ)
    (stk : Fin s → List Bool) : Fin s → List Bool :=
  Function.update (Function.update stk counter []) dst (List.replicate (4*n) false ++ stk dst)

theorem zeroFill_trace {r s : ℕ} (counter dst : Fin s) (v p : Fin r)
    (hcd : counter ≠ dst) (_hvp : v ≠ p)
    (count : List Bool) (regs : Fin r → Bool) (stk : Fin s → List Bool)
    (hc : stk counter = count) :
    Trace (zeroFillProgram counter dst v p) (7*count.length+2)
      ⟨some 0,regs,stk⟩
      ⟨some 7,readRegs regs v p none,zeroFillStacks counter dst count.length stk⟩ := by
  induction count generalizing regs stk with
  | nil =>
      refine  .cons (b := ⟨some 1,readRegs regs v p none,Function.update stk counter []⟩) ?_ ?_
      · simp [step,execInstr,hc]
      · refine  .cons (b := ⟨some 7,readRegs regs v p none,
          zeroFillStacks counter dst 0 stk⟩) ?_ ( .refl _)
        simp [step,execInstr,readRegs,zeroFillStacks,hcd.symm]
  | cons bit rest ih =>
      let r₁ := readRegs regs v p (some bit)
      let r₂ := Function.update r₁ v false
      let s₁ := Function.update stk counter rest
      let s₂ := Function.update s₁ dst (false::false::false::false::stk dst)
      have hc' : s₂ counter = rest := by simp [s₂,s₁,hcd]
      have ht := ih r₂ s₂ hc'
      have hr : readRegs r₂ v p none = readRegs regs v p none := by
        funext i
        by_cases h1 : i=v <;> by_cases h2 : i=p <;>
          simp [r₂,r₁,readRegs,Function.update_apply,h1,h2]
      have hs : zeroFillStacks counter dst rest.length s₂ =
          zeroFillStacks counter dst (bit::rest).length stk := by
        funext i
        by_cases hd : i=dst
        · subst i
          simp only [zeroFillStacks,Function.update_self,s₂,List.length_cons,Nat.mul_add,
            Nat.mul_one,List.replicate_add]
          simp [List.append_assoc,List.replicate_succ]
        · by_cases hi : i=counter
          · subst i; simp [zeroFillStacks,hd]
          · simp [zeroFillStacks,s₂,s₁,hd,hi]
      rw [hr,hs] at ht
      have hrun : Trace (zeroFillProgram counter dst v p) (7*rest.length+2+7)
          ⟨some 0,regs,stk⟩
          ⟨some 7,readRegs regs v p none,zeroFillStacks counter dst (bit::rest).length stk⟩ := by
        refine  .cons (b := ⟨some 1,r₁,s₁⟩) ?_ ?_
        · simp [step,execInstr,hc,r₁,s₁]
        · refine  .cons (b := ⟨some 2,r₁,s₁⟩) ?_ ?_
          · simp [step,execInstr,r₁,readRegs]
          · refine  .cons (b := ⟨some 3,r₂,s₁⟩) ?_ ?_
            · simp [step,execInstr,r₂]
            · refine  .cons (b := ⟨some 4,r₂,Function.update s₁ dst (false::stk dst)⟩) ?_ ?_
              · simp [step,execInstr,r₂,s₁,hcd.symm]
              · refine  .cons (b := ⟨some 5,r₂,Function.update s₁ dst (false::false::stk dst)⟩) ?_ ?_
                · simp [step,execInstr,r₂]
                · refine  .cons (b := ⟨some 6,r₂,Function.update s₁ dst (false::false::false::stk dst)⟩) ?_ ?_
                  · simp [step,execInstr,r₂]
                  · refine  .cons (b := ⟨some 0,r₂,s₂⟩) ?_ ht
                    simp [step,execInstr,r₂,s₂]
      convert hrun using 1

theorem zeroFill_eval {r s : ℕ} (counter dst : Fin s) (v p : Fin r)
    (hcd : counter ≠ dst) (hvp : v ≠ p) (d : State r s) :
    Eval (.call (zeroFillProgram counter dst v p)) (7*(d.stacks counter).length+3) d
      ⟨readRegs d.regs v p none,zeroFillStacks counter dst (d.stacks counter).length d.stacks⟩ := by
  apply Eval.call
  have h := zeroFill_trace counter dst v p hcd hvp (d.stacks counter) d.regs d.stacks rfl
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [StructuredProgram.State.withPC,zeroFillProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
