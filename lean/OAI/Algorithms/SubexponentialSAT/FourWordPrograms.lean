import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Four runtime-width words in flat and bank representations

Eight distinct caller ports hold a flat record, unary field width, counter,
temporary stack, and four bank words. The number four is fixed in the control;
the field width is exclusively stack data.
-/

namespace SubexponentialSAT.FourWordPrograms

open BitProgram StackRoutines StructuredCalls SubexpScanPrimitives

abbrev Words := Fin 4 → List Bool

def flatWords (words : Words) : List Bool :=
  words 0 ++ (words 1 ++ (words 2 ++ words 3))

def wordPort {s : ℕ} (ports : Fin 8 ↪ Fin s) (i : Fin 4) : Fin s :=
  ports (Fin.natAdd 4 i)

@[simp] private theorem ports_eq {s : ℕ} (ports : Fin 8 ↪ Fin s) (i j : Fin 8) :
    ports i = ports j ↔ i = j := ports.injective.eq_iff

private theorem five_injective {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (a b c d e : Fin 8) (h : Function.Injective (![a,b,c,d,e] : Fin 5 → Fin 8)) :
    Function.Injective (![ports a,ports b,ports c,ports d,ports e] : Fin 5 → Fin s) := by
  have heq : (![ports a,ports b,ports c,ports d,ports e] : Fin 5 → Fin s) =
      ports ∘ ![a,b,c,d,e] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact ports.injective.comp h

private theorem ports_ext {s : ℕ} (ports : Fin 8 ↪ Fin s) {f g : Stacks (Fin s)}
    (hi : ∀ i, f (ports i) = g (ports i))
    (ho : ∀ j, (∀ i, j ≠ ports i) → f j = g j) : f = g := by
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact hi i
  · exact ho j (fun i h => hj ⟨i, h.symm⟩)

/-- Ports 0/1/2/3 are flat input, width, counter, and temporary; ports 4–7
receive the four words in their original bit order. -/
abbrev splitCmd {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Cmd r s :=
  .seq (takeWord (ports 1) (ports 2) (ports 3) (ports 0) (ports 4) value present)
    (.seq (takeWord (ports 1) (ports 2) (ports 3) (ports 0) (ports 5) value present)
      (.seq (takeWord (ports 1) (ports 2) (ports 3) (ports 0) (ports 6) value present)
        (takeWord (ports 1) (ports 2) (ports 3) (ports 0) (ports 7) value present)))

def splitStacks {s : ℕ} (ports : Fin 8 ↪ Fin s) (words : Words) (rest : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update stk (ports 0) rest)
          (ports 4) (words 0 ++ stk (ports 4)))
        (ports 5) (words 1 ++ stk (ports 5)))
      (ports 6) (words 2 ++ stk (ports 6)))
    (ports 7) (words 3 ++ stk (ports 7))

theorem split_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (words : Words) (rest widthWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = flatWords words ++ rest) (hw : stk (ports 1) = widthWord)
    (hlen : ∀ i, (words i).length = widthWord.length)
    (hc : stk (ports 2) = []) (ht : stk (ports 3) = []) :
    Eval (splitCmd ports value present) (56 * widthWord.length + 44) ⟨regs, stk⟩
      ⟨readRegs regs value present none, splitStacks ports words rest stk⟩ := by
  let d : State r s := ⟨regs, stk⟩
  let d₁ := afterTake d (ports 0) (ports 4) value present (words 0)
    (words 1 ++ (words 2 ++ (words 3 ++ rest)))
  let d₂ := afterTake d₁ (ports 0) (ports 5) value present (words 1)
    (words 2 ++ (words 3 ++ rest))
  let d₃ := afterTake d₂ (ports 0) (ports 6) value present (words 2) (words 3 ++ rest)
  have a := takeWord_eval d (ports 1) (ports 2) (ports 3) (ports 0) (ports 4) value present
    (five_injective ports 1 2 3 0 4 (by decide)) hvp (words 0)
    (words 1 ++ (words 2 ++ (words 3 ++ rest)))
    (by simpa [d, flatWords, List.append_assoc] using hs) hc ht
    (by simp [d, hw, hlen])
  have b := takeWord_eval d₁ (ports 1) (ports 2) (ports 3) (ports 0) (ports 5) value present
    (five_injective ports 1 2 3 0 5 (by decide)) hvp (words 1)
    (words 2 ++ (words 3 ++ rest))
    (by simp [d₁, afterTake]) (by simpa [d₁, d, afterTake] using hc)
    (by simpa [d₁, d, afterTake] using ht) (by simp [d₁, d, afterTake, hw, hlen])
  have c := takeWord_eval d₂ (ports 1) (ports 2) (ports 3) (ports 0) (ports 6) value present
    (five_injective ports 1 2 3 0 6 (by decide)) hvp (words 2) (words 3 ++ rest)
    (by simp [d₂, afterTake]) (by simpa [d₂, d₁, d, afterTake] using hc)
    (by simpa [d₂, d₁, d, afterTake] using ht)
    (by simp [d₂, d₁, d, afterTake, hw, hlen])
  have e := takeWord_eval d₃ (ports 1) (ports 2) (ports 3) (ports 0) (ports 7) value present
    (five_injective ports 1 2 3 0 7 (by decide)) hvp (words 3) rest
    (by simp [d₃, afterTake]) (by simpa [d₃, d₂, d₁, d, afterTake] using hc)
    (by simpa [d₃, d₂, d₁, d, afterTake] using ht)
    (by simp [d₃, d₂, d₁, d, afterTake, hw, hlen])
  have hfinal : afterTake d₃ (ports 0) (ports 7) value present (words 3) rest =
      (⟨readRegs regs value present none, splitStacks ports words rest stk⟩ : State r s) := by
    apply state_ext
    · simp [d₃, d₂, d₁, d, afterTake, readRegs_reset]
    · apply ports_ext ports
      · intro i
        fin_cases i <;> simp [d₃, d₂, d₁, d, afterTake, splitStacks]
      · intro j hj
        simp [d₃, d₂, d₁, d, afterTake, splitStacks, hj]
  have total := a.seq (b.seq (c.seq e))
  rw [hfinal] at total
  dsimp [splitCmd]
  convert total using 1 ; simp [hlen] ; omega

/-- Copy the words in reverse call order so their flat output order is 0,1,2,3.
The word bank is preserved. No width is needed for packing. -/
abbrev packCmd {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Cmd r s :=
  .seq (.call (copyProgram (ports 7) (ports 0) (ports 3) value present))
    (.seq (.call (copyProgram (ports 6) (ports 0) (ports 3) value present))
      (.seq (.call (copyProgram (ports 5) (ports 0) (ports 3) value present))
        (.call (copyProgram (ports 4) (ports 0) (ports 3) value present))))

def bankWords {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s)) : Words :=
  fun i => stk (wordPort ports i)

def packStacks {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update stk (ports 0) (flatWords (bankWords ports stk) ++ stk (ports 0))

theorem pack_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (ht : stk (ports 3) = []) :
    Eval (packCmd ports value present) (7 * (flatWords (bankWords ports stk)).length + 20)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, packStacks ports stk⟩ := by
  let d : State r s := ⟨regs, stk⟩
  let d₁ := afterCopy d (ports 7) (ports 0) value present
  let d₂ := afterCopy d₁ (ports 6) (ports 0) value present
  let d₃ := afterCopy d₂ (ports 5) (ports 0) value present
  have a := copy_eval d (ports 7) (ports 0) (ports 3) value present
    (by simp) (by simp) (by simp) hvp ht
  have b := copy_eval d₁ (ports 6) (ports 0) (ports 3) value present
    (by simp) (by simp) (by simp) hvp (by simpa [d₁, d, afterCopy, copyStacks] using ht)
  have c := copy_eval d₂ (ports 5) (ports 0) (ports 3) value present
    (by simp) (by simp) (by simp) hvp (by simpa [d₂, d₁, d, afterCopy, copyStacks] using ht)
  have e := copy_eval d₃ (ports 4) (ports 0) (ports 3) value present
    (by simp) (by simp) (by simp) hvp
    (by simpa [d₃, d₂, d₁, d, afterCopy, copyStacks] using ht)
  have hfinal : afterCopy d₃ (ports 4) (ports 0) value present =
      (⟨readRegs regs value present none, packStacks ports stk⟩ : State r s) := by
    apply state_ext
    · simp [d₃, d₂, d₁, d, afterCopy, readRegs_reset]
    · apply ports_ext ports
      · intro i
        fin_cases i <;> simp [d₃, d₂, d₁, d, afterCopy, copyStacks, packStacks,
          flatWords, bankWords, wordPort, List.append_assoc]
      · intro j hj
        simp [d₃, d₂, d₁, d, afterCopy, copyStacks, packStacks, hj]
  have total := a.seq (b.seq (c.seq e))
  rw [hfinal] at total
  dsimp [packCmd]
  convert total using 1 ;
    simp [d₃, d₂, d₁, d, afterCopy, copyStacks, flatWords, bankWords, wordPort] ; omega

abbrev splitProgram {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 69 :=
  compiled (splitCmd ports value present) (ports 0) (ports 4)

abbrev packProgram {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 33 :=
  compiled (packCmd ports value present) (ports 4) (ports 0)

theorem splitProgram_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (words : Words) (rest widthWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = flatWords words ++ rest) (hw : stk (ports 1) = widthWord)
    (hlen : ∀ i, (words i).length = widthWord.length)
    (hc : stk (ports 2) = []) (ht : stk (ports 3) = []) :
    @Trace r s (size (splitCmd ports value present) + 1)
      (splitProgram ports value present) (56 * widthWord.length + 45)
      ⟨some (splitProgram ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, splitStacks ports words rest stk⟩ := by
  have t := compiled_halt_trace
    (split_eval ports value present hvp words rest widthWord regs stk hs hw hlen hc ht)
    (ports 0) (ports 4)
  simpa [splitProgram, StructuredProgram.State.withPC, Nat.add_assoc] using t

theorem packProgram_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (ht : stk (ports 3) = []) :
    @Trace r s (size (packCmd ports value present) + 1)
      (packProgram ports value present) (7 * (flatWords (bankWords ports stk)).length + 21)
      ⟨some (packProgram ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, packStacks ports stk⟩ := by
  have t := compiled_halt_trace (pack_eval ports value present hvp regs stk ht) (ports 4) (ports 0)
  simpa [packProgram, StructuredProgram.State.withPC, Nat.add_assoc] using t

@[simp] theorem splitStacks_source {s : ℕ} (ports : Fin 8 ↪ Fin s) (words : Words)
    (rest : List Bool) (stk : Stacks (Fin s)) :
    splitStacks ports words rest stk (ports 0) = rest := by simp [splitStacks]

theorem splitStacks_word {s : ℕ} (ports : Fin 8 ↪ Fin s) (words : Words)
    (rest : List Bool) (stk : Stacks (Fin s)) (i : Fin 4) :
    splitStacks ports words rest stk (wordPort ports i) = words i ++ stk (wordPort ports i) := by
  fin_cases i <;> simp [splitStacks, wordPort]

theorem splitStacks_frame {s : ℕ} (ports : Fin 8 ↪ Fin s) (words : Words)
    (rest : List Bool) (stk : Stacks (Fin s)) (j : Fin s)
    (h0 : j ≠ ports 0) (hw : ∀ i, j ≠ wordPort ports i) :
    splitStacks ports words rest stk j = stk j := by
  have h4 := hw 0
  have h5 := hw 1
  have h6 := hw 2
  have h7 := hw 3
  simpa [splitStacks, wordPort] using
    (show splitStacks ports words rest stk j = stk j from by
      simp [splitStacks, h0, show j ≠ ports 4 from h4, show j ≠ ports 5 from h5,
        show j ≠ ports 6 from h6, show j ≠ ports 7 from h7])

theorem packStacks_source {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s)) :
    packStacks ports stk (ports 0) = flatWords (bankWords ports stk) ++ stk (ports 0) := by
  simp [packStacks]

theorem packStacks_frame {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s))
    (j : Fin s) (hj : j ≠ ports 0) : packStacks ports stk j = stk j := by
  simp [packStacks, hj]

theorem packProgram_trace_uniform {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (width : ℕ) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (ht : stk (ports 3) = []) (hlen : ∀ i, (stk (wordPort ports i)).length = width) :
    @Trace r s (size (packCmd ports value present) + 1)
      (packProgram ports value present) (28 * width + 21)
      ⟨some (packProgram ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, packStacks ports stk⟩ := by
  have t := packProgram_trace ports value present hvp regs stk ht
  have hf : (flatWords (bankWords ports stk)).length = 4 * width := by
    simp [flatWords, bankWords, hlen]
    omega
  rw [hf] at t
  convert t using 1
  omega

end SubexponentialSAT.FourWordPrograms

end OAI.Algorithms
