import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Store := Fin 256 → List Bool

def ExecutesIn (cmd : Code) (budget : ℕ) (before after : Store) : Prop :=
  ∀ regs : Fin 16 → Bool, ∃ n regs', n ≤ budget ∧
    Eval cmd n ⟨regs, before⟩ ⟨regs', after⟩

theorem ExecutesIn.seq {a b : Code} {ca cb : ℕ} {s t u : Store}
    (ha : ExecutesIn a ca s t) (hb : ExecutesIn b cb t u) :
    ExecutesIn (.seq a b) (ca + cb) s u := by
  intro regs
  obtain ⟨na, ra, hna, hea⟩ := ha regs
  obtain ⟨nb, rb, hnb, heb⟩ := hb ra
  exact ⟨na + nb, rb, Nat.add_le_add hna hnb, hea.seq heb⟩

theorem ExecutesIn.mono {cmd : Code} {a b : ℕ} {s t : Store}
    (h : ExecutesIn cmd a s t) (hab : a ≤ b) : ExecutesIn cmd b s t := by
  intro regs
  obtain ⟨n, regs', hn, he⟩ := h regs
  exact ⟨n, regs', hn.trans hab, he⟩

theorem copy_run (src dst : Fin 256) (s : Store)
    (hsd : src ≠ dst) (hst : src ≠ 120) (htd : (120 : Fin 256) ≠ dst)
    (htmp : s 120 = []) :
    ExecutesIn (copy src dst) (7 * (s src).length + 5) s
      (Function.update s dst (s src ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [copy, afterCopy, StackRoutines.copyStacks] using
    SubexpScanPrimitives.copy_eval (⟨regs, s⟩ : Data) src dst 120 0 1
      hsd hst htd (by decide) htmp

theorem takeCell_run (src dst : Fin 256) (s : Store) (bits rest : List Bool)
    (hdist : Function.Injective (![104, 121, 122, src, dst] : Fin 5 → Fin 256))
    (hsrc : s src = bits ++ rest) (hcounter : s 121 = []) (htmp : s 122 = [])
    (hwidth : (s 104).length = bits.length) :
    ExecutesIn (takeCell src dst) (14 * bits.length + 11) s
      (Function.update (Function.update s src rest) dst (bits ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  exact SubexpScanPrimitives.takeWord_eval (⟨regs, s⟩ : Data)
    104 121 122 src dst 0 1 hdist (by decide) bits rest hsrc hcounter htmp hwidth

theorem clear_run (src : Fin 256) (s : Store) :
    ExecutesIn (clear src) (2 * (s src).length + 3) s (Function.update s src []) := by
  intro regs
  exact ⟨_, readRegs regs 0 1 none, le_rfl, clear_eval ⟨regs, s⟩ src⟩

theorem appendIndex_run (index : Fin 256) (s : Store) :
    ExecutesIn (appendIndex index) 2 s (Function.update s index (false :: s index)) := by
  intro regs
  exact ⟨2, Function.update regs 0 false, le_rfl, appendIndex_eval ⟨regs, s⟩ index⟩

theorem popToken_run (counter : Fin 256) (s : Store) (bit : Bool) (rest : List Bool)
    (hcounter : s counter = bit :: rest) :
    ExecutesIn (popToken counter) 1 s (Function.update s counter rest) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (some bit), le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop counter 0 1)
    (⟨regs, s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, hcounter] using Eval.base h

/-- Runtime buffers, in order: left, right, accumulator, output index, row
index, row fuel, right suffix, cell fuel, current coefficient, left operand,
right operand. All other stacks form the scalar-service/caller frame. -/
abbrev Buffers := Fin 11 → List Bool

def bufferPorts : Fin 11 ↪ Fin 256 :=
  ⟨![100, 101, 102, 103, 105, 106, 108, 109, 110, 198, 199], by decide⟩

/-- Proof-level state embedding; the executable code uses fixed numeric ports. -/
noncomputable def buffers (base : Store) (w : Buffers) : Store :=
  Function.extend bufferPorts w base

@[simp] theorem buffers_port (base : Store) (w : Buffers) (i : Fin 11) :
    buffers base w (bufferPorts i) = w i := bufferPorts.injective.extend_apply _ _ _

theorem buffers_frame (base : Store) (w : Buffers) (j : Fin 256)
    (hj : ¬ ∃ i, bufferPorts i = j) : buffers base w j = base j :=
  Function.extend_apply' _ _ _ hj

theorem buffers_update (base : Store) (w : Buffers) (i : Fin 11) (v : List Bool) :
    buffers base (Function.update w i v) = Function.update (buffers base w) (bufferPorts i) v :=
  ProgramLinking.extend_update bufferPorts.injective w base i v

@[simp] theorem buffers_100 (base : Store) (w : Buffers) : buffers base w 100 = w 0 := buffers_port base w 0
@[simp] theorem buffers_101 (base : Store) (w : Buffers) : buffers base w 101 = w 1 := buffers_port base w 1
@[simp] theorem buffers_102 (base : Store) (w : Buffers) : buffers base w 102 = w 2 := buffers_port base w 2
@[simp] theorem buffers_103 (base : Store) (w : Buffers) : buffers base w 103 = w 3 := buffers_port base w 3
@[simp] theorem buffers_105 (base : Store) (w : Buffers) : buffers base w 105 = w 4 := buffers_port base w 4
@[simp] theorem buffers_106 (base : Store) (w : Buffers) : buffers base w 106 = w 5 := buffers_port base w 5
@[simp] theorem buffers_108 (base : Store) (w : Buffers) : buffers base w 108 = w 6 := buffers_port base w 6
@[simp] theorem buffers_109 (base : Store) (w : Buffers) : buffers base w 109 = w 7 := buffers_port base w 7
@[simp] theorem buffers_110 (base : Store) (w : Buffers) : buffers base w 110 = w 8 := buffers_port base w 8
@[simp] theorem buffers_198 (base : Store) (w : Buffers) : buffers base w 198 = w 9 := buffers_port base w 9
@[simp] theorem buffers_199 (base : Store) (w : Buffers) : buffers base w 199 = w 10 := buffers_port base w 10
@[simp] theorem buffers_104 (base : Store) (w : Buffers) : buffers base w 104 = base 104 :=
  buffers_frame base w 104 (by decide)
@[simp] theorem buffers_120 (base : Store) (w : Buffers) : buffers base w 120 = base 120 :=
  buffers_frame base w 120 (by decide)
@[simp] theorem buffers_121 (base : Store) (w : Buffers) : buffers base w 121 = base 121 :=
  buffers_frame base w 121 (by decide)
@[simp] theorem buffers_122 (base : Store) (w : Buffers) : buffers base w 122 = base 122 :=
  buffers_frame base w 122 (by decide)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
