import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 41
abbrev Store := Fin 41 → List Bool

def ports (counter : Fin 41) : UnaryForPrograms.Ports 8 41 := ⟨counter, 0, 7⟩

def state (base : Store) (counter output : Fin 41) (regs : Fin 8 → Bool)
    (n : ℕ) (tail : List Bool) : Data :=
  ⟨regs, Function.update (Function.update base counter (List.replicate n true)) output tail⟩

abbrev cells (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => cells f n ++ f n

abbrev command (counter : Fin 41) (body : Cmd 8 41) : Cmd 8 41 :=
  UnaryForPrograms.forCmd (ports counter) body

theorem popped_succ (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (regs : Fin 8 → Bool) (n : ℕ) (tail : List Bool) :
    UnaryForPrograms.popped (ports counter) (state base counter output regs (n+1) tail) =
      state base counter output (readRegs regs 0 7 (some true)) n tail := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, ports, state, hco, List.replicate_succ]
  · funext i
    by_cases hi : i = counter
    · subst i; simp [UnaryForPrograms.popped, ports, state, hco, List.replicate_succ]
    · by_cases hio : i = output
      · subst i; simp [UnaryForPrograms.popped, ports, state, Ne.symm hco]
      · simp [UnaryForPrograms.popped, ports, state, hi, hio]

theorem popped_zero (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (regs : Fin 8 → Bool) (tail : List Bool) :
    UnaryForPrograms.popped (ports counter) (state base counter output regs 0 tail) =
      state base counter output (readRegs regs 0 7 none) 0 tail := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, ports, state, hco]
  · funext i
    by_cases hi : i = counter
    · subst i; simp [UnaryForPrograms.popped, ports, state, hco]
    · by_cases hio : i = output
      · subst i; simp [UnaryForPrograms.popped, ports, state, Ne.symm hco]
      · simp [UnaryForPrograms.popped, ports, state, hi, hio]

/-- The callback premise is a genuine native trace. It receives index i as
the remaining unary counter and must preserve that counter and the frame. -/
theorem command_eval (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (body : Cmd 8 41) (f : ℕ → List Bool) (K n : ℕ)
    (step : ∀ i, i < n → ∀ regs tail, ∃ cost rf, cost ≤ K ∧
      Eval body cost (state base counter output regs i tail)
        (state base counter output rf i (f i ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ n*(K+2)+2 ∧
      Eval (command counter body) cost (state base counter output regs n tail)
        (state base counter output rf 0 (cells f n ++ tail)) := by
  suffices h : ∃ costs cost rf, cost ≤ n*(K+2)+2 ∧
      UnaryForPrograms.Visits (ports counter) body costs cost
        (state base counter output regs n tail)
        (state base counter output rf 0 (cells f n ++ tail)) by
    obtain ⟨costs,cost,rf,hb,he⟩ := h
    exact ⟨cost,rf,hb,he.eval⟩
  induction n generalizing regs tail with
  | zero =>
      refine ⟨[],2,readRegs regs 0 7 none,by simp,?_⟩
      have h := UnaryForPrograms.Visits.done (p := ports counter) (body := body)
        (state base counter output regs 0 tail) (by simp [ports,state,hco])
      simpa only [popped_zero base counter output hco, cells, List.nil_append] using h
  | succ n ih =>
      obtain ⟨nb,rb,hnb,hbody⟩ := step n (by omega) (readRegs regs 0 7 (some true)) tail
      obtain ⟨costs,nt,rt,hnt,ht⟩ := ih (fun i hi => step i (by omega)) rb (f n ++ tail)
      refine ⟨nb::costs,nb+nt+2,rt,by nlinarith,?_⟩
      have he := UnaryForPrograms.Visits.step
        (p := ports counter) (body := body)
        (d := state base counter output regs (n+1) tail)
        (by simp [ports,state,hco,List.replicate_succ])
        (by simpa only [popped_succ base counter output hco] using hbody)
        (by rw [popped_succ base counter output hco]; simp [ports,state,hco]) ht
      simpa only [cells, List.append_assoc] using he

theorem cells_length (f : ℕ → List Bool) (width n : ℕ)
    (hw : ∀ i, i < n → (f i).length = width) : (cells f n).length = n*width := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
      rw [cells, List.length_append, ih (fun i hi => hw i (by omega)), hw n (by omega)]
      simp [Nat.add_mul]

abbrev copyAndScan (source counter _output scratch : Fin 41) (body : Cmd 8 41) : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram source counter scratch (0 : Fin 8) 1))
    (command counter body)

def scanBudget (n K : ℕ) : ℕ := n*(K+9)+7

theorem copyAndScan_eval (base : Store) (source counter output scratch : Fin 41)
    (hsc : source ≠ counter) (hst : source ≠ scratch) (htc : scratch ≠ counter)
    (hso : source ≠ output) (hco : counter ≠ output) (hto : scratch ≠ output)
    (body : Cmd 8 41) (f : ℕ → List Bool) (K n : ℕ)
    (hs : base source = List.replicate n true) (hc : base counter = [])
    (ht : base scratch = [])
    (step : ∀ i, i < n → ∀ regs tail, ∃ cost rf, cost ≤ K ∧
      Eval body cost (state base counter output regs i tail)
        (state base counter output rf i (f i ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ scanBudget n K ∧
      Eval (copyAndScan source counter output scratch body) cost
        ⟨regs, Function.update base output tail⟩
        ⟨rf, Function.update base output (cells f n ++ tail)⟩ := by
  let a : Data := ⟨regs, Function.update base output tail⟩
  let b := SubexpScanPrimitives.afterCopy a source counter 0 1
  have he := SubexpScanPrimitives.copy_eval a source counter scratch 0 1
    hsc hst htc (by decide) (by simp [a,hto,ht])
  have hbs : b = state base counter output b.regs n tail := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simp only [b,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,a,state]
    funext i
    by_cases hio : i = output
    · subst i; simp [Ne.symm hco]
    · by_cases hic : i = counter
      · subst i; simp [hco,hso,hc,hs]
      · simp [hio,hic]
  obtain ⟨nt,rt,hnt,hloop⟩ := command_eval base counter output hco body f K n step b.regs tail
  rw [←hbs] at hloop
  have hfinal : state base counter output rt 0 (cells f n ++ tail) =
      ⟨rt, Function.update base output (cells f n ++ tail)⟩ := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simp [state,←hc]
  rw [hfinal] at hloop
  refine ⟨(7*n+5)+nt,rt,?_,?_⟩
  · dsimp [scanBudget]; nlinarith
  · have hlen : (a.stacks source).length = n := by simp [a,hso,hs]
    simpa only [copyAndScan,hlen] using he.seq hloop

abbrev tableCommand (entry : Cmd 8 41) : Cmd 8 41 :=
  copyAndScan 37 24 22 38
    (copyAndScan 37 25 22 38 (copyAndScan 37 26 22 38 entry))

def tableCells (f : ℕ → ℕ → ℕ → List Bool) (n : ℕ) : List Bool :=
  cells (fun k => cells (fun i => cells (fun j => f i j k) n) n) n

/-- The exact runtime budget for three source-preserving unary loops. -/
def tableBudget (n K : ℕ) : ℕ := scanBudget n (scanBudget n (scanBudget n K))

theorem tableBudget_polynomial (n K : ℕ) :
    tableBudget n K ≤ 23*(n+1)^3*(K+1) := by
  simp only [tableBudget,scanBudget]
  nlinarith [Nat.zero_le (n^3*K),Nat.zero_le (n^2*K),Nat.zero_le (n*K)]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
