import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafSupportInputProgramConvert
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramSupports
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! The actual support enumerator and format converter share one private bank. -/
namespace SubexponentialSAT.SqrtLog.LeafSupportInputProgram.Local

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram
open SubexponentialSAT.SqrtLog.MomentsAssembly (rawFrames)

abbrev Data := State 10 13
abbrev Code := Cmd 10 13

def generatorInput (regs : Fin 10 → Bool) (depth budget : List Bool) : State 10 10 :=
  ⟨regs,![[],[],[],[],[],[],[],[],depth,budget]⟩
def generatorOutput (regs : Fin 10 → Bool) (rows : List (List Bool)) (budget : List Bool) : State 10 10 :=
  ⟨regs,![ProgramEncoding.encodeRecords rows,ProgramEncoding.encodeRecords SupportProgram.Steps.alphabet,
    [],[],[],[false],[],[],[],budget]⟩

theorem generator_runsIn (regs : Fin 10 → Bool) (depth budget : List Bool) :
    ∃ rf rows, SupportProgram.Correct depth.length budget.length rows ∧
      RunsIn SupportProgram.program (SupportProgram.Loop.cost depth.length budget.length+29)
        ((generatorInput regs depth budget).withPC (some SupportProgram.program.entry))
        ((generatorOutput rf rows budget).withPC none) := by
  let a := generatorInput regs depth budget
  have ha : SupportProgram.Init.Empty budget a := by
    constructor
    · intro i hi8 hi9; fin_cases i <;> simp_all [a,generatorInput]
    · rfl
  obtain ⟨i,hi,c,hinit,hc,hdepth⟩ := SupportProgram.Init.command_eval budget a ha
  obtain ⟨j,b,hj,hb,hend,hloop⟩ := SupportProgram.Loop.command_eval budget c hc
  rcases hb with ⟨rows,hcorrect,h0,h1,h2,h3,h4,h5,h6,h7,h9⟩
  have hd : c.stacks 8=depth := hdepth
  rw [hd] at hj hcorrect
  have hs : b=generatorOutput b.regs rows budget := by
    change StructuredProgram.State.mk b.regs b.stacks = _
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext z; fin_cases z <;> simp_all []
  have he := compiled_halt_trace (hinit.seq hloop) 8 0
  change Trace SupportProgram.program (i+j+1) (a.withPC (some SupportProgram.program.entry)) (b.withPC none) at he
  rw [hs] at he
  exact ⟨b.regs,rows,hcorrect,i+j+1,by omega,he⟩

def state (regs : Fin 10 → Bool) (cells : Fin 10 → List Bool)
    (depth budget output : List Bool) : Data :=
  ⟨regs,![cells 0,cells 1,cells 2,cells 3,cells 4,cells 5,cells 6,cells 7,cells 8,cells 9,
    depth,budget,output]⟩
def initial (regs : Fin 10 → Bool) (depth budget : List Bool) : Data :=
  state regs (fun _ => []) depth budget []
def final (regs : Fin 10 → Bool) (depth budget output : List Bool) : Data :=
  state regs (fun _ => []) depth budget output

@[simp] theorem state_genPort (regs : Fin 10 → Bool) (cells : Fin 10 → List Bool)
    (depth budget output : List Bool) (i : Fin 10) :
    (state regs cells depth budget output).stacks (Fin.castAdd 3 i) = cells i := by
  fin_cases i <;> rfl

abbrev genPorts : Fin 10 → Fin 13 := Fin.castAdd 3
abbrev convRegs : Fin 3 → Fin 10 := Fin.castAdd 7
def convPorts : Fin 3 → Fin 13 := ![0,2,12]
def copyDepth : Code := .call (StackRoutines.copyProgram 10 8 7 0 1)
def copyBudget : Code := .call (StackRoutines.copyProgram 11 9 7 0 1)
def generate : Code := .call (ProgramLinking.liftProgram SupportProgram.program id genPorts)
def convert : Code := .call (ProgramLinking.liftProgram Convert.program convRegs convPorts)
def command : Code := .seq copyDepth (.seq copyBudget (.seq generate (.seq convert
  (WorkspaceCleanupProgram.command 0 1 [1,5,9]))))
def program := compiled command 10 12

def cost (n J : ℕ) : ℕ :=
  7*n+9*J+SupportProgram.Loop.cost n J+SupportProgram.count n J*(11*n+13)+73

private theorem embed_generator_eq (rb rg : Fin 10 → Bool) (depth budget : List Bool)
    (rows : List (List Bool)) :
    embedState id genPorts (state rb (generatorInput rb depth budget).stacks depth budget [])
        (generatorOutput rg rows budget) =
      state rg (generatorOutput rg rows budget).stacks depth budget [] := by
  apply embedState_eq_of_ports id genPorts
    (state rb (generatorInput rb depth budget).stacks depth budget [])
    (state rg (generatorOutput rg rows budget).stacks depth budget [])
    (generatorOutput rg rows budget) Function.injective_id (Fin.castAdd_injective _ _)
  · intro i
    rfl
  · intro i hi
    exact (hi ⟨i, rfl⟩).elim
  · intro i
    exact state_genPort rg (generatorOutput rg rows budget).stacks depth budget [] i
  · intro i hi
    fin_cases i <;>
      simp_all [Fin.exists_fin_succ, genPorts, state]

theorem program_runsIn (regs : Fin 10 → Bool) (depth budget : List Bool) :
    ∃ rf rows, SupportProgram.Correct depth.length budget.length rows ∧
      RunsIn program (cost depth.length budget.length)
        ((initial regs depth budget).withPC (some program.entry))
        ((final rf depth budget (rawFrames rows.reverse)).withPC none) := by
  let d := initial regs depth budget
  let ra := readRegs regs (0 : Fin 10) 1 none
  let a := state ra (generatorInput ra depth []).stacks depth budget []
  have ha : Eval copyDepth (7*depth.length+5) d a := by
    have h := copy_eval (10 : Fin 13) 8 7 (0 : Fin 10) 1 (by decide) (by decide)
      (by decide) (by decide) d (by rfl)
    rw [show d.stacks 10 = depth by rfl] at h
    have hout : StructuredProgram.State.mk (readRegs d.regs 0 1 none)
        (StackRoutines.copyStacks 10 8 d.stacks) = a := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [d, ra, initial, state, generatorInput, StackRoutines.copyStacks]
    rw [hout] at h
    exact h
  let rb := readRegs ra (0 : Fin 10) 1 none
  let b := state rb (generatorInput rb depth budget).stacks depth budget []
  have hb : Eval copyBudget (7*budget.length+5) a b := by
    have h := copy_eval (11 : Fin 13) 9 7 (0 : Fin 10) 1 (by decide) (by decide)
      (by decide) (by decide) a (by rfl)
    rw [show a.stacks 11 = budget by rfl] at h
    have hout : StructuredProgram.State.mk (readRegs a.regs 0 1 none)
        (StackRoutines.copyStacks 11 9 a.stacks) = b := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [ a, rb, state, generatorInput, StackRoutines.copyStacks]
    rw [hout] at h
    exact h
  obtain ⟨rg,rows,hcorrect,tg,htg,heg⟩ := generator_runsIn rb depth budget
  have hproj : projectState id genPorts b=generatorInput rb depth budget := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [←hproj] at heg
  have hgen := eval_call_from_state SupportProgram.program id genPorts b
    Function.injective_id (Fin.castAdd_injective _ _) heg
  let g := state rg (generatorOutput rg rows budget).stacks depth budget []
  have hg : embedState id genPorts b (generatorOutput rg rows budget)=g := by
    exact embed_generator_eq rb rg depth budget rows
  change Eval generate tg b (embedState id genPorts b (generatorOutput rg rows budget)) at hgen
  rw [hg] at hgen
  obtain ⟨tc,htc,hec⟩ := Convert.program_runsIn (rg ∘ convRegs) rows
  have hprojn : projectState convRegs convPorts g =
      Convert.state (rg ∘ convRegs) (ProgramEncoding.encodeRecords rows) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [←hprojn] at hec
  have hconv := eval_call_from_state Convert.program convRegs convPorts g
    (Fin.castAdd_injective _ _) (by decide) hec
  let cout := Convert.state ![false,true,false] [] [] (rawFrames rows.reverse)
  let e := embedState convRegs convPorts g cout
  let rest : Fin 10 → List Bool := ![[],ProgramEncoding.encodeRecords SupportProgram.Steps.alphabet,
    [],[],[],[false],[],[],[],budget]
  let c := state e.regs rest depth budget (rawFrames rows.reverse)
  have hc : e=c := by
    apply embedState_eq_of_ports convRegs convPorts g c cout (Fin.castAdd_injective _ _) (by decide)
    · intro i; exact embedState_register convRegs convPorts g cout (Fin.castAdd_injective _ _) i
    · intro i hi; exact embedState_register_frame convRegs convPorts g cout i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [Fin.exists_fin_succ,convPorts,c,rest,g,state,generatorOutput]
  change Eval convert tc g e at hconv
  rw [hc] at hconv
  have hclean := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([1,5,9] : List (Fin 13)) (by decide) c
  let rf := (WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([1,5,9] : List (Fin 13)) c).regs
  have hs : WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([1,5,9] : List (Fin 13)) c =
      final rf depth budget (rawFrames rows.reverse) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [c,state,rest,BankRoutines.clearBankStacks]
  rw [hs] at hclean
  have hlen : rows.length=SupportProgram.count depth.length budget.length :=
    SupportProgram.correct_length _ _ _ hcorrect
  have hcost := Convert.cost_uniform rows depth.length (fun row hr => ((hcorrect.2 row).mp hr).1)
  rw [hcost,hlen] at htc
  refine ⟨rf,rows,hcorrect, (7*depth.length+5)+((7*budget.length+5)+(tg+(tc+
    WorkspaceCleanupProgram.cost ([1,5,9] : List (Fin 13)) c)))+1,?_,?_⟩
  · simp [WorkspaceCleanupProgram.cost,c,state,rest,SupportProgram.Steps.alphabet,
      ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.frame,cost]
    omega
  · exact compiled_halt_trace (ha.seq (hb.seq (hgen.seq (hconv.seq hclean)))) 10 12

end SubexponentialSAT.SqrtLog.LeafSupportInputProgram.Local

end OAI.Algorithms
