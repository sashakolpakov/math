import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateProgram

namespace OAI.Algorithms

/-! Named physical fields at the boundaries of the one-node template
builder. Point and factor work are empty except during their concrete calls. -/

namespace SubexponentialSAT.SubexpTemplateProgram

open BitProgram StructuredCalls

abbrev Context := SubexpBlueprintFactor.Context

structure Work where
  point : Word := []
  factorInput : Word := []
  base : Word := []
  support : Word := []
  input : Word := []
  block : Word := []
  group : Word := []
  term : Word := []
  factors : Word := []
  payload : Word := []
  parser : Word := []
  increment : Word := []
  bank : Word := []
  output : Word := []
  outer : Word := []
  scratch : Word := []

/-- The point stream is dynamic Work data. The Context's pointStream field
is ignored here and supplied afresh to each factor call. -/
def state (ctx : Context) (regs : Fin 8 → Bool) (w : Work) : Data :=
  ⟨regs,fun i => match i.val with
    | 66 => ctx.sourceModulus | 73 => ctx.sourceReduction | 74 => ctx.sourceWidth
    | 79 => ctx.targetWidth | 90 => ctx.sourceZero | 91 => w.point
    | 92 => ctx.targetModulus | 93 => ctx.targetMinusOne
    | 94 => List.replicate ctx.dimension true | 95 => List.replicate ctx.indexWidth true
    | 100 => w.factorInput | 128 => w.base | 129 => w.support | 130 => w.input
    | 131 => w.block | 132 => w.group | 133 => w.term | 134 => w.factors
    | 135 => w.payload | 136 => w.parser | 137 => w.increment | 138 => w.bank
    | 139 => w.output | 140 => w.outer | 141 => w.scratch | _ => []⟩

def serviceState (ctx : Context) (regs : Fin 8 → Bool) (input : Word) : Data :=
  state ctx regs {input:=input}

theorem state_stack_eq (ctx : Context) (regs : Fin 8 → Bool) (w : Work) (i : Fin 142) :
    (state ctx regs w).stacks i =
      if i=66 then ctx.sourceModulus else if i=73 then ctx.sourceReduction
      else if i=74 then ctx.sourceWidth else if i=79 then ctx.targetWidth
      else if i=90 then ctx.sourceZero else if i=91 then w.point
      else if i=92 then ctx.targetModulus else if i=93 then ctx.targetMinusOne
      else if i=94 then List.replicate ctx.dimension true
      else if i=95 then List.replicate ctx.indexWidth true
      else if i=100 then w.factorInput else if i=128 then w.base
      else if i=129 then w.support else if i=130 then w.input
      else if i=131 then w.block else if i=132 then w.group
      else if i=133 then w.term else if i=134 then w.factors
      else if i=135 then w.payload else if i=136 then w.parser
      else if i=137 then w.increment else if i=138 then w.bank
      else if i=139 then w.output else if i=140 then w.outer
      else if i=141 then w.scratch else [] := by
  fin_cases i <;> rfl

def factorContext (ctx : Context) (w : Work) : SubexpBlueprintFactor.Context :=
  {ctx with pointStream:=w.point}

theorem factorPorts_injective : Function.Injective factorPorts := Fin.castAdd_injective _ _

theorem project_factor (ctx : Context) (regs : Fin 8 → Bool) (w : Work) :
    projectState id factorPorts (state ctx regs w) =
      SubexpBlueprintFactor.serviceState (factorContext ctx w) regs w.factorInput := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem embed_factor (ctx : Context) (oldRegs regs : Fin 8 → Bool) (w : Work) (input : Word) :
    embedState id factorPorts (state ctx oldRegs w)
      (SubexpBlueprintFactor.serviceState (factorContext ctx w) regs input) =
      state ctx regs {w with factorInput:=input} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id factorPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    exact congrArg (fun d : State 8 128 => d.stacks i)
      (project_factor ctx regs {w with factorInput:=input})
  · intro i hi
    have h100 : i ≠ 100 := fun h => hi ⟨100,h.symm⟩
    simp only [state_stack_eq,h100,ite_false]

end SubexponentialSAT.SubexpTemplateProgram

end OAI.Algorithms
