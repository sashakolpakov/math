import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd

namespace OAI.Algorithms

/-! Caller-state interface for the actual four-word modular-addition program.
Only the mapped left/result port and the consumed right port change. -/

namespace SubexponentialSAT.SubexpFlatAddCall

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

abbrev programAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s) :
    Program r s (size SubexpFlatAdd.coefficientAdd + 1) :=
  ProgramLinking.liftProgram SubexpFlatAdd.program registers ports

abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s) : Cmd r s :=
  .call (programAt registers ports)

def resultStacks {s : ℕ} (ports : Fin 20 ↪ Fin s) (result : List Bool)
    (stk : Fin s → List Bool) : Fin s → List Bool :=
  Function.update (Function.update stk (ports 8) result) (ports 9) []

theorem resultStacks_frame {s : ℕ} (ports : Fin 20 ↪ Fin s) (result : List Bool)
    (stk : Fin s → List Bool) (j : Fin s) (h8 : j ≠ ports 8) (h9 : j ≠ ports 9) :
    resultStacks ports result stk j = stk j := by
  simp only [resultStacks, Function.update_noteq h9, Function.update_noteq h8]

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

theorem ready_stacks_update (ri rf : Fin 8 → Bool)
    (modulus left right result width : List Bool) (frame : Fin 6 → List Bool) :
    (SubexpFlatAdd.ready rf modulus result [] width [] frame).stacks =
      Function.update (Function.update
        (SubexpFlatAdd.ready ri modulus left right width [] frame).stacks 8 result) 9 [] := by
  funext i
  fin_cases i <;> simp [SubexpFlatAdd.ready, SubexpFlatAdd.state,
    SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod]

theorem ready_regs (regs : Fin 8 → Bool)
    (modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    (SubexpFlatAdd.ready regs modulus left right width packed frame).regs = regs := rfl

/-- The register and stack embeddings are static wiring. The input words and
their width are runtime data, and the bound comes from the actual add trace. -/
theorem callAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (d : State r s) (frame : Fin 6 → List Bool)
    (hstore : ∀ i, d.stacks (ports i) =
      (SubexpFlatAdd.ready (fun j => d.regs (registers j)) M.bits
        (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b) width [] frame).stacks i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          resultStacks ports (SubexpFlatAdd.encode
            (SubexpPreparedQuartic.binaryAdd p μ M a b).1) d.stacks⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpFlatAdd.program_runs_uniform p μ M
    (fun i => d.regs (registers i)) a b width frame hw
  have hl := ProgramLinking.liftProgram_trace SubexpFlatAdd.program registers ports
    (⟨none, d.regs, d.stacks⟩ : Cfg r s (size SubexpFlatAdd.coefficientAdd + 1))
    registers.injective ports.injective ht
  have hr := extend_agree registers (fun i => d.regs (registers i)) d.regs (fun _ => rfl)
  have hi := extend_agree ports
    (SubexpFlatAdd.ready (fun j => d.regs (registers j)) M.bits
      (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b) width [] frame).stacks
    d.stacks hstore
  have ho : Function.extend ports
      (SubexpFlatAdd.ready rf M.bits
        (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
        [] width [] frame).stacks d.stacks =
      resultStacks ports (SubexpFlatAdd.encode
        (SubexpPreparedQuartic.binaryAdd p μ M a b).1) d.stacks := by
    rw [ready_stacks_update (fun j => d.regs (registers j)) rf M.bits
      (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b)]
    rw [ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hi]
    rfl
  refine ⟨n, rf, hn, Eval.call _ ?_⟩
  simpa only [callAt, programAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    id_eq, ready_regs, hr, hi, ho, StructuredProgram.State.withPC] using hl

end SubexponentialSAT.SubexpFlatAddCall

end OAI.Algorithms
