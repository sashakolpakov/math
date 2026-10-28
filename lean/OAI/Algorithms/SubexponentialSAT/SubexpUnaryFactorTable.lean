import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryRowEnumeration

namespace OAI.Algorithms

/-! A closed p-row unary-factor constructor, including counter setup and cleanup. -/

namespace SubexponentialSAT.SubexpUnaryFactorTable

open BitProgram StructuredCalls StackRoutines CounterPrograms
open SubexpUnaryRowProgram (Data Clean)
open SubexpUnaryRowEnumeration (rows ports bodyBound)

def Ready (d : Data) : Prop :=
  Clean d.stacks ∧ d.stacks 10 = [] ∧ d.stacks 11 = [] ∧ d.stacks 12 = []

def prepared (d : Data) : Data := ⟨readRegs d.regs 0 1 none, copyStacks 13 11 d.stacks⟩

abbrev setup : Cmd 8 16 := .call (copyProgram 13 11 12 0 1)

theorem setup_eval (d : Data) (hs : d.stacks 12 = []) :
    Eval setup (7 * (d.stacks 13).length + 5) d (prepared d) :=
  .call _ (ListRegisterProgram.copy_run 13 11 12 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks hs)

abbrev clear (i : Fin 16) : Cmd 8 16 := .call (clearProgram i 0 1)
def cleared (i : Fin 16) (d : Data) : Data := ⟨readRegs d.regs 0 1 none, clearStacks i d.stacks⟩

theorem clear_eval (i : Fin 16) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

abbrev finish : Cmd 8 16 := .seq (clear 10) (clear 11)
def finished (d : Data) : Data := cleared 11 (cleared 10 d)

theorem finish_eval (d : Data) :
    Eval finish (2 * (d.stacks 10).length + 2 * (d.stacks 11).length + 6) d (finished d) := by
  have he := (clear_eval 10 d).seq (clear_eval 11 (cleared 10 d))
  convert he using 1 <;> simp [ finished, cleared, clearStacks] ; omega

abbrev command : Cmd 8 16 :=
  .seq setup (.seq (.call SubexpUnaryRowEnumeration.program) finish)

def table (width p : ℕ) : List Bool := rows width 0 p

@[simp] theorem table_length (width p : ℕ) : (table width p).length = p := by
  simp [table]

theorem table_reverse (width p : ℕ) :
    (table width p).reverse = (List.range' 0 p).map (SubexpUnaryRowProgram.answer width) := by
  simp [table, rows, List.map_reverse]

theorem command_eval (modulus width : List Bool) (d : Data)
    (hp : d.stacks 13 = modulus) (hw : d.stacks 14 = width)
    (hwidth : width.length ≤ modulus.length) (hr : Ready d) :
    ∃ t ≤ 199 * (value modulus + modulus.length + 1) ^ 2, ∃ e : Data,
      Eval command t d e ∧ Ready e ∧ e.stacks 13 = modulus ∧ e.stacks 14 = width ∧
      e.stacks 15 = table width.length (value modulus) ++ d.stacks 15 := by
  rcases hr with ⟨hc, h10, h11, h12⟩
  let a := prepared d
  have ha10 : a.stacks 10 = [] := by simpa [a, prepared, copyStacks] using h10
  have ha11 : a.stacks 11 = modulus := by simp [a, prepared, copyStacks, hp, h11]
  have ha12 : a.stacks 12 = [] := by simpa [a, prepared, copyStacks] using h12
  have ha13 : a.stacks 13 = modulus := by simpa [a, prepared, copyStacks] using hp
  have ha14 : a.stacks 14 = width := by simpa [a, prepared, copyStacks] using hw
  have ha15 : a.stacks 15 = d.stacks 15 := by simp [a, prepared, copyStacks]
  have hac : Clean a.stacks := by
    intro i
    have hi : i.castAdd 6 ≠ (11 : Fin 16) := by
      intro h; have hv := congrArg Fin.val h; change i.val = 11 at hv; omega
    simpa [a, prepared, copyStacks, hi] using hc i
  have hbound : value modulus < 2 ^ modulus.length := by
    rw [value_eq_toNat]
    exact SubexpFactorProgram.toNat_lt_pow_length modulus
  obtain ⟨b, ⟨n, hn, htrace⟩, hout, hb13, hb14, hbc, hb10, hb11, hb12, _⟩ :=
    SubexpUnaryRowEnumeration.program_runs modulus width a ha13 ha14 hac ha12
      (by simp [ha10]) (by simp [ha11]) hwidth
      (by simpa only [ha10, ha11, value, Nat.zero_add] using hbound)
  have hbudget := SubexpEnumerationSchedule.loopBudget_le (fun _ => bodyBound modulus)
    0 (value modulus) (value modulus) modulus.length (bodyBound modulus) (by intro i hi; exact le_rfl)
  have hn' : n ≤ 8 * modulus.length + 8 +
      (value modulus * (bodyBound modulus + 8 * value modulus + 16 * modulus.length + 24) + 1) := by
    simp only [SubexpEnumerationSchedule.programBudget, ports, ha10, ha11,
      List.length_nil, value, Nat.zero_add] at hn
    omega
  have hready : Ready (finished b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hi10 : i.castAdd 6 ≠ (10 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 10 at hv; omega
      have hi11 : i.castAdd 6 ≠ (11 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 11 at hv; omega
      simpa [finished, cleared, clearStacks, hi10, hi11] using hbc i
    · simp [finished, cleared, clearStacks]
    · simp [finished, cleared, clearStacks]
    · simpa [finished, cleared, clearStacks] using hb12
  let t := (7 * (d.stacks 13).length + 5) +
    (n + (2 * (b.stacks 10).length + 2 * (b.stacks 11).length + 6))
  refine ⟨t, ?_, finished b,
    (setup_eval d h12).seq ((Eval.call _ htrace).seq (finish_eval b)), hready, ?_, ?_, ?_⟩
  · dsimp [t]
    rw [hp]
    dsimp [bodyBound] at hn'
    nlinarith [Nat.zero_le (value modulus * modulus.length)]
  · simpa [finished, cleared, clearStacks] using hb13
  · simpa [finished, cleared, clearStacks] using hb14
  · simpa [finished, cleared, clearStacks, ha10, ha11, ha15, table, value] using hout

def program := compiled command 13 15

theorem program_runsIn (modulus width : List Bool) (d : Data)
    (hp : d.stacks 13 = modulus) (hw : d.stacks 14 = width)
    (hwidth : width.length ≤ modulus.length) (hr : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = modulus ∧ e.stacks 14 = width ∧
      e.stacks 15 = table width.length (value modulus) ++ d.stacks 15 ∧
      RunsIn program (200 * (value modulus + modulus.length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, hready, h13, h14, h15⟩ := command_eval modulus width d hp hw hwidth hr
  refine ⟨e, hready, h13, h14, h15, t + 1, ?_, compiled_halt_trace he 13 15⟩
  have hpos : 0 < (value modulus + modulus.length + 1) ^ 2 := pow_pos (by omega) _
  omega

theorem primitive_execution (modulus width : List Bool) (d : Data)
    (hp : d.stacks 13 = modulus) (hw : d.stacks 14 = width)
    (hwidth : width.length ≤ modulus.length) (hr : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = modulus ∧ e.stacks 14 = width ∧
      e.stacks 15 = table width.length (value modulus) ++ d.stacks 15 ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (200 * (value modulus + modulus.length + 1) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hp', hw', ho, hrun⟩ := program_runsIn modulus width d hp hw hwidth hr
  exact ⟨e, he, hp', hw', ho, BitProgram.primitive_execution program hrun⟩

end SubexponentialSAT.SubexpUnaryFactorTable

end OAI.Algorithms
