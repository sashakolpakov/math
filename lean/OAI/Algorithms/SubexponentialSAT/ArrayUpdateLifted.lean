import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms

namespace OAI.Algorithms

/-! Caller-state interfaces for the persistent packed-array routines. -/

namespace SubexponentialSAT.ArrayUpdateLifted

open BitProgram StackRoutines StructuredCalls ArrayUpdatePrograms

private theorem extend_restrict {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s)) :
    Function.extend ports (fun i => stk (ports i)) stk = stk := by
  classical
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact ports.injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hj

def readStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s) (record : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk (ports 2) []) (ports 1) (record ++ stk (ports 1))

def replaceStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s) (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk (ports 2) []) (ports 0)
    (earlier.flatten ++ (replacement ++ rest))

private theorem extend_read {s : ℕ} (ports : Fin 8 ↪ Fin s) (record : List Bool)
    (stk : Stacks (Fin s)) :
    Function.extend ports (readStacks record (fun i => stk (ports i))) stk =
      readStacksAt ports record stk := by
  simp only [readStacks, ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

private theorem extend_replace {s : ℕ} (ports : Fin 8 ↪ Fin s) (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin s)) :
    Function.extend ports (replaceStacks earlier replacement rest (fun i => stk (ports i))) stk =
      replaceStacksAt ports earlier replacement rest stk := by
  simp only [replaceStacks, ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

abbrev readProgramAt {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 38 :=
  ProgramLinking.liftProgram (readProgram value present) id ports

abbrev replaceProgramAt {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 44 :=
  ProgramLinking.liftProgram (replaceProgram value present) id ports

theorem readProgramAt_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hw : stk (ports 3) = widthWord) (hi : stk (ports 2) = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Trace (readProgramAt ports value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨some (readProgramAt ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, readStacksAt ports record stk⟩ := by
  have trace := readProgram_trace value present hvp earlier record rest widthWord indexWord
    regs (fun i => stk (ports i)) hs hw hi hiLen hrows hlen hc ht hb hp
  have lifted := ProgramLinking.liftProgram_trace (readProgram value present) id ports
    (⟨none, regs, stk⟩ : Cfg r s 38) Function.injective_id ports.injective trace
  simpa [readProgramAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, extend_read, extend_restrict] using lifted

theorem replaceProgramAt_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hn : stk (ports 1) = replacement) (hw : stk (ports 3) = widthWord)
    (hi : stk (ports 2) = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Trace (replaceProgramAt ports value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨some (replaceProgramAt ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, replaceStacksAt ports earlier replacement rest stk⟩ := by
  have trace := replaceProgram_trace value present hvp earlier record replacement rest widthWord
    indexWord regs (fun i => stk (ports i)) hs hn hw hi hiLen hrows hlen hnew hc ht hb hp
  have lifted := ProgramLinking.liftProgram_trace (replaceProgram value present) id ports
    (⟨none, regs, stk⟩ : Cfg r s 44) Function.injective_id ports.injective trace
  simpa [replaceProgramAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, extend_replace, extend_restrict] using lifted

theorem readProgramAt_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hw : stk (ports 3) = widthWord) (hi : stk (ports 2) = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Eval (.call (readProgramAt ports value present))
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, readStacksAt ports record stk⟩ :=
  .call _ (readProgramAt_trace ports value present hvp earlier record rest widthWord indexWord
    regs stk hs hw hi hiLen hrows hlen hc ht hb hp)

theorem replaceProgramAt_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hn : stk (ports 1) = replacement) (hw : stk (ports 3) = widthWord)
    (hi : stk (ports 2) = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Eval (.call (replaceProgramAt ports value present))
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, replaceStacksAt ports earlier replacement rest stk⟩ :=
  .call _ (replaceProgramAt_trace ports value present hvp earlier record replacement rest widthWord
    indexWord regs stk hs hn hw hi hiLen hrows hlen hnew hc ht hb hp)

theorem readStacksAt_frame {s : ℕ} (ports : Fin 8 ↪ Fin s) (record : List Bool)
    (stk : Stacks (Fin s)) (j : Fin s) (hi : j ≠ ports 2) (ho : j ≠ ports 1) :
    readStacksAt ports record stk j = stk j := by simp [readStacksAt, hi, ho]

theorem replaceStacksAt_frame {s : ℕ} (ports : Fin 8 ↪ Fin s) (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin s)) (j : Fin s)
    (hi : j ≠ ports 2) (ha : j ≠ ports 0) :
    replaceStacksAt ports earlier replacement rest stk j = stk j := by
  simp [replaceStacksAt, hi, ha]

end SubexponentialSAT.ArrayUpdateLifted

end OAI.Algorithms
