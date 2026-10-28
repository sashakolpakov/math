import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionKey
import OAI.Algorithms.SubexponentialSAT.SubexpJobFrames
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! The concrete callback used by the U/Z job iterator.  It builds a key,
normalizes its width, and emits the three-frame extraction record. -/

namespace SubexponentialSAT.SubexpExtractionJobProgram

open BitProgram StructuredCalls

abbrev Data := SubexpJobFrames.Data
abbrev Code := SubexpJobFrames.Code

structure KeyReady (d : Data) (xs : List Bool) (u z width : ℕ) : Prop where
  x : d.stacks 0 = xs
  u : d.stacks 4 = List.replicate u true
  z : d.stacks 5 = List.replicate z true
  width : d.stacks 3 = List.replicate width true
  raw : d.stacks 8 = []
  counter : d.stacks 9 = []
  key : d.stacks 10 = []
  temporary : d.stacks 11 = []

structure Ready (d : Data) (xs sourceBits : List Bool) (u z width : ℕ) : Prop where
  x : d.stacks 0 = xs
  source : d.stacks 1 = sourceBits
  u : d.stacks 4 = List.replicate u true
  z : d.stacks 5 = List.replicate z true
  width : d.stacks 3 = List.replicate width true
  raw : d.stacks 8 = []
  counter : d.stacks 9 = []
  key : d.stacks 10 = []
  temporary : d.stacks 11 = []
  inner : d.stacks 12 = []
  cached : d.stacks 15 = Encoding.frame sourceBits

theorem Ready.keyReady {d : Data} {xs source : List Bool} {u z width : ℕ}
    (h : Ready d xs source u z width) : KeyReady d xs u z width :=
  ⟨h.x, h.u, h.z, h.width, h.raw, h.counter, h.key, h.temporary⟩

def keyRegisters (i : Fin 2) : Fin 3 := Fin.castAdd 1 i
def keyPorts : Fin 8 → Fin 24 := ![0, 4, 5, 3, 8, 9, 10, 11]

theorem keyRegisters_injective : Function.Injective keyRegisters := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 3 => i.val) h)
theorem keyPorts_injective : Function.Injective keyPorts := by decide

def keyCall : Code := .call
  (ProgramLinking.liftProgram SubexpExtractionKey.program keyRegisters keyPorts)

def localRegs (d : Data) (i : Fin 2) : Bool := d.regs (keyRegisters i)

def afterKey (d : Data) (regs : Fin 2 → Bool) (raw count key : List Bool) : Data :=
  ⟨![regs 0, regs 1, d.regs 2],
    Function.update (Function.update (Function.update d.stacks 8 raw) 9 count) 10 key⟩

private theorem key_embed (d : Data) (xs : List Bool) (u z width : ℕ)
    (h : KeyReady d xs u z width) (regs : Fin 2 → Bool) (raw count key : List Bool) :
    embedState keyRegisters keyPorts d
      (SubexpExtractionKey.state regs xs (List.replicate u true) (List.replicate z true)
        (List.replicate width true) raw count key []) = afterKey d regs raw count key := by
  apply embedState_eq_of_ports _ _ _ _ _ keyRegisters_injective keyPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · rfl
  · intro i
    fin_cases i <;>
      simp [afterKey, keyPorts, SubexpExtractionKey.state, SubexpExtractionKey.storage,
        h.x, h.u, h.z, h.width, h.temporary]
  · intro i hi
    have h₈ : i ≠ 8 := fun e => hi ⟨4, e.symm⟩
    have h₉ : i ≠ 9 := fun e => hi ⟨5, e.symm⟩
    have h₁₀ : i ≠ 10 := fun e => hi ⟨6, e.symm⟩
    simp [afterKey, h₈, h₉, h₁₀]

private theorem afterKey_before (d : Data) (xs : List Bool) (u z width : ℕ)
    (h : KeyReady d xs u z width) : afterKey d (localRegs d) [] [] [] = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    by_cases h₈ : i = 8
    · subst i; simpa [afterKey] using h.raw.symm
    by_cases h₉ : i = 9
    · subst i; simpa [afterKey] using h.counter.symm
    by_cases h₁₀ : i = 10
    · subst i; simpa [afterKey] using h.key.symm
    simp [h₈, h₉, h₁₀]

theorem keyCall_eval_minimal (d : Data) (xs : List Bool) (u z width : ℕ)
    (h : KeyReady d xs u z width) :
    ∃ finalRegs, Eval keyCall (7 * (xs.length + u + z) + 11 * width + 28) d
      (afterKey d finalRegs ((SubexpExtractionKey.rawKey xs u z).drop width) []
        (SubexpExponentProgram.padTake width (SubexpExtractionKey.rawKey xs u z)).reverse) := by
  obtain ⟨finalRegs, he⟩ := SubexpExtractionKey.build_eval (localRegs d) xs u z width
  have ht := StructuredCalls.compiled_halt_trace he 0 6
  have hcall := eval_call_lifted SubexpExtractionKey.program keyRegisters keyPorts d
    keyRegisters_injective keyPorts_injective ht
  rw [key_embed d xs u z width h, afterKey_before d xs u z width h,
    key_embed d xs u z width h] at hcall
  refine ⟨finalRegs, ?_⟩
  convert hcall using 1
  rfl

theorem keyCall_eval (d : Data) (xs source : List Bool) (u z width : ℕ)
    (h : Ready d xs source u z width) :
    ∃ finalRegs, Eval keyCall (7 * (xs.length + u + z) + 11 * width + 28) d
      (afterKey d finalRegs ((SubexpExtractionKey.rawKey xs u z).drop width) []
        (SubexpExponentProgram.padTake width (SubexpExtractionKey.rawKey xs u z)).reverse) :=
  keyCall_eval_minimal d xs u z width h.keyReady

def clearRaw : Code := .call (StackRoutines.clearProgram 8 0 1)
def rawCleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 8 []⟩

theorem clearRaw_eval (d : Data) :
    Eval clearRaw (2 * (d.stacks 8).length + 3) d (rawCleared d) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run 8 0 1 d.regs d.stacks

def normalizedKey (xs : List Bool) (u z width : ℕ) : List Bool :=
  SubexpExponentProgram.padTake width (SubexpExtractionKey.rawKey xs u z)

def job (xs source : List Bool) (u z width : ℕ) : SubexpMomentProgram.Job :=
  SubexpJobFrames.job (normalizedKey xs u z width) source z

theorem normalizedKey_eq_fixedKey {D : ℕ} (a : Fin D → ℕ) (u z : ℕ)
    (h : SymbolicCost.Retained D (a, u, z)) :
    normalizedKey (SymbolicCost.unaryWords (List.ofFn a)) u z
      (SubexpSymbolicCost.indexBits D) = SubexpSymbolicCost.fixedKey (a, u, z) := by
  have hlen := SubexpSymbolicCost.retained_index_bits (a, u, z) h
  unfold normalizedKey
  rw [SubexpExtractionKey.rawKey_eq, SubexpExponentProgram.padTake,
    List.take_of_length_le hlen]
  rfl

theorem job_eq_fixedKey {D : ℕ} (a : Fin D → ℕ) (source : List Bool) (u z : ℕ)
    (h : SymbolicCost.Retained D (a, u, z)) :
    job (SymbolicCost.unaryWords (List.ofFn a)) source u z
      (SubexpSymbolicCost.indexBits D) =
      ⟨List.replicate z true, SubexpSymbolicCost.fixedKey (a, u, z), source⟩ := by
  unfold job
  rw [normalizedKey_eq_fixedKey a u z h]
  rfl

/-- The same concrete key builder can emit the retained slot master without
constructing or carrying a moment source. -/
def emitKey : Code := .seq keyCall (.seq clearRaw (SubexpJobFrames.writer 14))

theorem emitKey_eval (d : Data) (xs : List Bool) (u z width : ℕ)
    (h : KeyReady d xs u z width) :
    ∃ ticks e, ticks ≤ 100 * (xs.length + u + z + width + 1) ∧
      Eval emitKey ticks d e ∧
      e.stacks = Function.update d.stacks 14
        (true :: (Encoding.frame (normalizedKey xs u z width) ++ d.stacks 14)) := by
  obtain ⟨regs, hk⟩ := keyCall_eval_minimal d xs u z width h
  let k := afterKey d regs ((SubexpExtractionKey.rawKey xs u z).drop width) []
    (normalizedKey xs u z width).reverse
  let c := rawCleared k
  have hc := clearRaw_eval k
  have hw := SubexpJobFrames.writer_eval 14 c (by decide) (by decide) (by decide)
  have hkey : c.stacks 10 = (normalizedKey xs u z width).reverse := by
    simp [c, k, rawCleared, afterKey]
  refine ⟨_, SubexpJobFrames.written 14 c, ?_, hk.seq (hc.seq hw), ?_⟩
  · have hlength : (normalizedKey xs u z width).length = width :=
      SubexpExponentProgram.padTake_length _ _
    have hdrop : ((SubexpExtractionKey.rawKey xs u z).drop width).length ≤
        xs.length + u + z + 2 := by
      simp only [List.length_drop, SubexpExtractionKey.rawKey, List.length_append,
        SymbolicCost.unaryWord, List.length_replicate, List.length_singleton]
      omega
    simp only [hkey, List.length_reverse, hlength]
    have hraw : (k.stacks 8).length =
        ((SubexpExtractionKey.rawKey xs u z).drop width).length := by simp [k, afterKey]
    rw [hraw]
    omega
  · funext i
    by_cases h14 : i = 14 <;> by_cases h10 : i = 10 <;>
      by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
      simp_all [SubexpJobFrames.written, c, k, rawCleared, afterKey,
        h.raw, h.counter, h.key]

def emitOne : Code := .seq keyCall (.seq clearRaw SubexpJobFrames.emitPrepared)

/-- The emitted job has the exact source/key/index format expected by the
extraction phase.  Every stack other than the output stack is preserved. -/
theorem emitOne_eval (d : Data) (xs source : List Bool) (u z width : ℕ)
    (h : Ready d xs source u z width) :
    ∃ ticks e, ticks ≤ 100 * (xs.length + source.length + u + z + width + 2) ∧
      Eval emitOne ticks d e ∧
      e.stacks = Function.update d.stacks 14
        (true :: (Encoding.frame (job xs source u z width).encode ++ d.stacks 14)) := by
  obtain ⟨finalRegs, hk⟩ := keyCall_eval d xs source u z width h
  let k := afterKey d finalRegs ((SubexpExtractionKey.rawKey xs u z).drop width) []
    (normalizedKey xs u z width).reverse
  let c := rawCleared k
  have hc := clearRaw_eval k
  have ht : c.stacks 11 = [] := by simp [c, k, rawCleared, afterKey, h.temporary]
  have hf := SubexpJobFrames.emitPrepared_eval c ht
  have hkey : c.stacks 10 = (normalizedKey xs u z width).reverse := by
    simp [c, k, rawCleared, afterKey]
  have hsource : c.stacks 15 = Encoding.frame source := by
    simp [c, k, rawCleared, afterKey, h.cached]
  have hz : c.stacks 5 = List.replicate z true := by
    simp [c, k, rawCleared, afterKey, h.z]
  have hi : c.stacks 12 = [] := by simp [c, k, rawCleared, afterKey, h.inner]
  refine ⟨_, SubexpJobFrames.frameResult c, ?_, hk.seq (hc.seq hf), ?_⟩
  · have hfc := SubexpJobFrames.frameCost_eq c (normalizedKey xs u z width) source z
      hkey hsource hz hi
    have hlength : (normalizedKey xs u z width).length = width :=
      SubexpExponentProgram.padTake_length _ _
    have hdrop : ((SubexpExtractionKey.rawKey xs u z).drop width).length ≤
        xs.length + u + z + 2 := by
      simp only [List.length_drop, SubexpExtractionKey.rawKey, List.length_append,
        SymbolicCost.unaryWord, List.length_replicate, List.length_singleton]
      omega
    simp only [hfc, hlength]
    have hraw : (k.stacks 8).length =
        ((SubexpExtractionKey.rawKey xs u z).drop width).length := by simp [k, afterKey]
    rw [hraw]
    omega
  · funext i
    by_cases hout : i = 14
    · subst i
      simpa [job, c, k, rawCleared, afterKey] using
        SubexpJobFrames.frameResult_output c (normalizedKey xs u z width) source z
          hkey hsource hz hi
    · by_cases hk' : i = 10
      · subst i
        simp [SubexpJobFrames.frameResult_clean, h.key]
      · by_cases hin : i = 12
        · subst i
          simp [SubexpJobFrames.frameResult_clean, h.inner]
        · rw [SubexpJobFrames.frameResult_preserved c i hk' hin hout]
          by_cases hr : i = 8 <;> by_cases hc' : i = 9 <;>
            simp_all [c, k, rawCleared, afterKey, h.raw, h.counter]

end SubexponentialSAT.SubexpExtractionJobProgram

end OAI.Algorithms
