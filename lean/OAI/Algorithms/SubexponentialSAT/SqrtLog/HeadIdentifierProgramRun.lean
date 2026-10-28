import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramLoop
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def baseStacks (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  fun i => if i=30 then unary rows.length else if i=31 then low else if i=32 then unary z
    else if i=33 then rows.flatten else if i=38 then unary W else []

def input (regs : Fin 16 → Bool) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨regs,baseStacks rows low W z⟩

def result (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (baseStacks rows low W z) 0
      (ProgramEncoding.encodeRecords ((chosenIds (predicate rows low z) rows.length).map unary)))
      1 (zeros (count (predicate rows low z) rows.length))⟩

def setup : Code := .seq (copy 30 39) (Subexp.TupleProgram.pushConst 0 0 false)
def command : Code := .seq setup (.seq loop RegisterResetProgram.all)
def program := compiled command 30 0

def preparedStacks (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  Function.update (Function.update (baseStacks rows low W z) 39 (unary rows.length)) 0 [false]

theorem setup_eval (regs : Fin 16 → Bool) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    ∃ e, Eval setup (7*rows.length+7) (input regs rows low W z) e ∧
      e.stacks=preparedStacks rows low W z := by
  let d := input regs rows low W z
  let a := afterCopy d 30 39 0 1
  let e := Subexp.TupleProgram.pushedState 0 0 false a
  have h1 : Eval (copy 30 39) (7*rows.length+5) d a := by
    have he := copy_eval d 30 39 42 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    simpa [Subexp.SupportSelectionProgram.copy, a, d, input, baseStacks] using he
  have h2 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false a
  refine ⟨e,?_,?_⟩
  · convert h1.seq h2 using 1 ; simp [setup]
  · funext i
    by_cases h39 : i=39
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    by_cases h0 : i=0
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    · simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks,h0,h39]

def budget (n W L z : ℕ) := n*(visitBound n W L z+2)+7*n+26

theorem program_runsIn (regs : Fin 16 → Bool) (rows : List (List Bool)) (low : List Bool)
    (W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) :
    RunsIn program (budget rows.length W low.length z)
      ((input regs rows low W z).withPC (some program.entry))
      ((result rows low W z).withPC none) := by
  obtain ⟨d,hs,hsd⟩ := setup_eval regs rows low W z
  have hdClean : Clean d := by
    intro i hi
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [hsd,preparedStacks,baseStacks]
  obtain ⟨costs,nl,e,hv,hnl,hse⟩ := loop_visits rows low W z hrows rows.length d le_rfl
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks]) hdClean
  have hz := RegisterResetProgram.all_eval e
  have hout : RegisterResetProgram.zeroed e=result rows low W z := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [hse,hsd,preparedStacks,baseStacks,result,
        Subexp.SupportSelectionProgram.prefix_encode,ProgramEncoding.encodeRecords,
        Subexp.SupportSelectionProgram.indexWords,chosenIds]
  rw [hout] at hz
  have he := hs.seq (hv.eval.seq hz)
  refine ⟨7*rows.length+7+(nl+16)+1,?_,compiled_halt_trace he 30 0⟩
  unfold budget
  omega

theorem budget_polynomial (n W L z : ℕ) :
    budget n W L z ≤ 300*(n+W+L+z+1)^3 := by
  let s := n+W+L+z+1
  have hn : n ≤ s := by dsimp [s]; omega
  have hW : W ≤ s := by dsimp [s]; omega
  have hL : L ≤ s := by dsimp [s]; omega
  have hz : z ≤ s := by dsimp [s]; omega
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs23 : s^2 ≤ s^3 := Nat.pow_le_pow_right hs (by decide)
  have hv : visitBound n W L z ≤ 200*s^2 := by
    calc
      _ ≤ s*(14*s+17)+15*s+22+22*s+9*s+10*s+2*s+43 := by
        unfold visitBound lookupCost
        gcongr
      _ ≤ 200*s^2 := by nlinarith
  have hm : n*(visitBound n W L z+2) ≤ 202*s^3 := by
    calc
      _ ≤ s*(200*s^2+2) := Nat.mul_le_mul hn (by omega)
      _ ≤ 202*s^3 := by nlinarith
  unfold budget
  change n*(visitBound n W L z+2)+7*n+26 ≤ 300*s^3
  nlinarith

theorem program_primitive (regs : Fin 16 → Bool) (rows : List (List Bool)) (low : List Bool)
    (W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program*budget rows.length W low.length z)
      (primitiveCfg program ((input regs rows low W z).withPC (some program.entry)))
      (primitiveCfg program ((result rows low W z).withPC none)) :=
  primitive_execution program (program_runsIn regs rows low W z hrows)

theorem result_frame (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 64) (h0 : i≠0) (h1 : i≠1) :
    (result rows low W z).stacks i=baseStacks rows low W z i := by
  simp [result,h0,h1]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
