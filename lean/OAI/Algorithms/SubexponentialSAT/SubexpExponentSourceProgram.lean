import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSeed
import OAI.Algorithms.SubexponentialSAT.SubexpExponentHost

namespace OAI.Algorithms

/-! The concrete exponent-stream setup.  It starts with the unary dimension,
constructs the initial coordinate vector and budget, invokes the actual
successor controller, and clears its work stacks. -/

namespace SubexponentialSAT.SubexpExponentSourceProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def seedRegisters : Fin 2 → Fin 16 := Fin.castAdd 14
def seedPorts : Fin 4 → Fin 128 := ![2, 112, 113, 114]

theorem seedRegisters_injective : Function.Injective seedRegisters := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem seedPorts_injective : Function.Injective seedPorts := by decide

def generatorPorts : Fin 6 ↪ Fin 128 where
  toFun := ![112, 113, 114, 110, 115, 116]
  inj' := by decide

def seedCall : Code := .call
  (ProgramLinking.liftProgram SubexpExponentSeed.program seedRegisters seedPorts)

def clear (i : Fin 128) : Code := .call (StackRoutines.clearProgram i 0 1)

def cleared (i : Fin 128) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

theorem clear_eval (i : Fin 128) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run i 0 1 d.regs d.stacks

theorem seedCall_eval (d : Data) (D : ℕ)
    (hD : d.stacks 2 = List.replicate D true)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = []) (h114 : d.stacks 114 = []) :
    ∃ e, Eval seedCall (11 * D + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 112 (List.replicate D false))
        113 (List.replicate (2 * D + 1) true) := by
  let regs : Fin 2 → Bool := fun i => d.regs (seedRegisters i)
  let before : StructuredProgram.State 2 4 :=
    ⟨regs, SubexpExponentSeed.storage (List.replicate D true) [] [] []⟩
  let after : StructuredProgram.State 2 4 :=
    ⟨![true, false], SubexpExponentSeed.storage (List.replicate D true)
      (List.replicate D false) (List.replicate (2 * D + 1) true) []⟩
  have hb : embedState seedRegisters seedPorts d before = d := by
    apply embedState_eq_of_ports _ _ _ _ _ seedRegisters_injective seedPorts_injective
    · intros; rfl
    · intros; rfl
    · intro i
      fin_cases i <;>
        simp [seedPorts, before, SubexpExponentSeed.storage, hD, h112, h113, h114]
    · intros; rfl
  have ht := SubexpExponentSeed.program_trace D regs
  change Trace SubexpExponentSeed.program (11 * D + 7)
    (before.withPC (some SubexpExponentSeed.program.entry)) (after.withPC none) at ht
  have he := eval_call_lifted SubexpExponentSeed.program seedRegisters seedPorts d
    seedRegisters_injective seedPorts_injective ht
  rw [hb] at he
  refine ⟨embedState seedRegisters seedPorts d after, he, ?_⟩
  funext i
  by_cases hi : ∃ j, seedPorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [embedState_stack seedRegisters seedPorts d after seedPorts_injective]
    fin_cases j <;> simp [seedPorts, after, SubexpExponentSeed.storage, hD, h114]
  · rw [embedState_stack_frame seedRegisters seedPorts d after i hi]
    have h1 : i ≠ 112 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ 113 := fun h => hi ⟨2, h.symm⟩
    simp [h1, h2]

def command : Code := .seq seedCall
  (.seq (SubexpExponentHost.call generatorPorts) (.seq (clear 113) (clear 114)))

def program := compiled command 2 110

def output (D : ℕ) : List Bool :=
  Encoding.encodeList SubexpExponentController.momentWord
    (Algorithm.exponentList D (2 * D + 1)).reverse

def work : List (Fin 128) := [110, 112, 113, 114, 115, 116]

theorem command_eval (d : Data) (D : ℕ)
    (hD : d.stacks 2 = List.replicate D true)
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ ticks e, ticks ≤ 25 * (3 * D + 2) * (3 * D + 1).choose D + 17 * D + 20 ∧
      Eval command ticks d e ∧ e.stacks = Function.update d.stacks 110 (output D) := by
  obtain ⟨s, hs, hss⟩ := seedCall_eval d D hD
    (hwork 112 (by decide)) (hwork 113 (by decide)) (hwork 114 (by decide))
  have hinit : ∀ i, s.stacks (generatorPorts i) =
      (SubexpExponentHost.initial s D (2 * D + 1)).stacks i := by
    intro i
    fin_cases i <;>
      simp [generatorPorts, hss, SubexpExponentHost.initial,
        SubexpExponentController.encoded, SubexpExponentController.state,
        SubexpExponentController.storage6,
        hwork 110 (by decide), hwork 114 (by decide),
        hwork 115 (by decide), hwork 116 (by decide)]
  obtain ⟨gn, g, regs, hgn, hg, hgs, hframe, _⟩ :=
    SubexpExponentHost.call_eval generatorPorts s D (2 * D + 1) hinit
  have g112 : g.stacks 112 = [] := by
    simpa [generatorPorts] using (hgs 0).trans (SubexpExponentHost.final_work regs D (2 * D + 1)).1
  have g113 : g.stacks 113 = List.replicate (2 * D + 1) true := by
    simpa [generatorPorts] using (hgs 1).trans (SubexpExponentHost.final_work regs D (2 * D + 1)).2.1
  have g114 : g.stacks 114 = List.replicate D false := by
    simpa [generatorPorts] using (hgs 2).trans (SubexpExponentHost.final_work regs D (2 * D + 1)).2.2.1
  have g110 : g.stacks 110 = output D := by
    simpa [generatorPorts, output] using (hgs 3).trans (SubexpExponentHost.final_output regs D (2 * D + 1))
  have g115 : g.stacks 115 = [] := by
    simpa [generatorPorts] using (hgs 4).trans (SubexpExponentHost.final_work regs D (2 * D + 1)).2.2.2.1
  have g116 : g.stacks 116 = [] := by
    simpa [generatorPorts] using (hgs 5).trans (SubexpExponentHost.final_work regs D (2 * D + 1)).2.2.2.2
  let a := cleared 113 g
  let e := cleared 114 a
  have ha := clear_eval 113 g
  have he := clear_eval 114 a
  have total := hs.seq (hg.seq (ha.seq he))
  refine ⟨_, e, ?_, total, ?_⟩
  · simp only [g113, List.length_replicate] at total ⊢
    have hlen : (a.stacks 114).length = D := by simp [a, cleared, g114]
    rw [hlen]
    have hnum : D + (2 * D + 1) = 3 * D + 1 := by omega
    rw [hnum] at hgn
    rw [show 3 * D + 1 + 1 = 3 * D + 2 by omega] at hgn
    omega
  · funext i
    by_cases hi : ∃ j, generatorPorts j = i
    · obtain ⟨j, rfl⟩ := hi
      fin_cases j <;>
        simp [generatorPorts, e, a, cleared, g110, g112, g115, g116,
          hwork 112 (by decide), hwork 113 (by decide), hwork 114 (by decide),
          hwork 115 (by decide), hwork 116 (by decide)]
    · have h110 : i ≠ 110 := fun h => hi ⟨3, h.symm⟩
      have h112 : i ≠ 112 := fun h => hi ⟨0, h.symm⟩
      have h113 : i ≠ 113 := fun h => hi ⟨1, h.symm⟩
      have h114 : i ≠ 114 := fun h => hi ⟨2, h.symm⟩
      simp [e, a, cleared, h110, h113, h114, hframe i hi, hss, h112]

theorem program_runs (d : Data) (D : ℕ)
    (hD : d.stacks 2 = List.replicate D true)
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ e : Data, RunsIn program
      (25 * (3 * D + 2) * (3 * D + 1).choose D + 17 * D + 21)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 110 (output D) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval d D hD hwork
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 2 110⟩, hs⟩

end SubexponentialSAT.SubexpExponentSourceProgram

end OAI.Algorithms
