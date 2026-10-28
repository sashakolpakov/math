import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramKey
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- Swapping the key helper's mask port protects the caller's beta on220. -/
def keyMap : Equiv.Perm (Fin 256) := Equiv.swap 214 220
def keyCommand : Code := liftCommand PerturbationProgram.Key.command 0 0 id keyMap

def keyBits (mask : List Bool) (j : ℕ) : List Bool :=
  PerturbationProgram.Key.bits (List.replicate j true) mask

def record (mask : List Bool) (j : ℕ) (coeff : List Bool) : List Bool :=
  Encoding.frame (keyBits mask j) ++ Encoding.frame coeff

private theorem embed_same (map : Fin 256 → Fin 256) (hm : Function.Injective map)
    (r rf : Fin 16 → Bool) (s : Store) :
    embedState id map (⟨r,s⟩ : Data) ⟨rf,s ∘ map⟩ = (⟨rf,s⟩ : Data) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hm
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; rfl
  · intro i hi; rfl

theorem key_run (s : Store) (mask : List Bool) (j : ℕ)
    (hm : s 214=mask) (hj : s 221=List.replicate j true)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[]) :
    ExecutesIn keyCommand (16*(j+mask.length)+40) s
      (Function.update s 222 (keyBits mask j).reverse) := by
  intro regs
  have hk221 : keyMap 221 = 221 := by decide
  have hk120 : keyMap 120 = 120 := by decide
  have hk222 : keyMap 222 = 222 := by decide
  have hk223 : keyMap 223 = 223 := by decide
  have hk224 : keyMap 224 = 224 := by decide
  have h := PerturbationProgram.Key.command_run (s ∘ keyMap)
    (List.replicate j true) mask
    (by simpa [Function.comp_def, hk221] using hj)
    (by simpa [Function.comp_def,keyMap] using hm)
    (by simpa [Function.comp_def, hk120] using h120)
    (by simpa [Function.comp_def, hk222] using h222)
    (by simpa [Function.comp_def, hk223] using h223)
    (by simpa [Function.comp_def, hk224] using h224)
  obtain ⟨n,rf,hn,he⟩ := h regs
  have hl := eval_liftCommand_from_state PerturbationProgram.Key.command 0 0
    id keyMap (⟨regs,s⟩ : Data) Function.injective_id keyMap.injective he
  have hout : embedState id keyMap (⟨regs,s⟩ : Data)
      ⟨rf,Function.update (s ∘ keyMap) 222 (keyBits mask j).reverse⟩ =
      (⟨rf,Function.update s 222 (keyBits mask j).reverse⟩ : Data) := by
    rw [embedState_update_stack id keyMap _ (⟨rf,s ∘ keyMap⟩ : Data)
      keyMap.injective 222 (keyBits mask j).reverse,embed_same keyMap keyMap.injective]
    rw [show keyMap 222=222 from by decide]
  change Eval keyCommand (n+1) (⟨regs,s⟩ : Data)
    (embedState id keyMap (⟨regs,s⟩ : Data)
      ⟨rf,Function.update (s ∘ keyMap) 222 (keyBits mask j).reverse⟩) at hl
  rw [hout] at hl
  refine ⟨n+1,rf,?_,?_⟩
  · simp only [List.length_replicate] at hn
    omega
  · exact hl

/-- Take one forward fixed-width cell and reverse it for the framed emitter. -/
def readCoefficient : Code := .seq (takeWord 211 226 227 240 228 0 1)
  (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))

theorem read_run (s : Store) (bits rest : List Bool)
    (hs : s 240=bits++rest) (hw : (s 211).length=bits.length)
    (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn readCoefficient (23*bits.length+18) s
      (Function.update (Function.update s 240 rest) 228 bits.reverse) := by
  intro regs
  let mid := afterTake (⟨regs,s⟩ : Data) 240 228 0 1 bits rest
  have h1 := takeWord_eval (⟨regs,s⟩ : Data) 211 226 227 240 228 0 1
    (by decide) (by decide) bits rest hs h226 h227 hw
  have h2 := reverse_eval mid 228 226 227 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [mid,afterTake,h226]) (by simp [mid,afterTake,h227])
  have he : afterReverse mid 228 0 1 =
      (⟨readRegs regs 0 1 none,
        Function.update (Function.update s 240 rest) 228 bits.reverse⟩ : Data) := by
    apply state_ext
    · simp [afterReverse,mid,afterTake,StackRoutines.readRegs_reset]
    · simp [afterReverse,mid,afterTake,StackRoutines.reverseStacks,h228]
  rw [he] at h2
  refine ⟨14*bits.length+11+(9*(mid.stacks 228).length+7),
    readRegs regs 0 1 none,?_,?_⟩
  · simp [mid,afterTake,h228]; omega
  · exact h1.seq h2

def emitMap : Fin 3 → Fin 256 := ![222,228,217]
def emitRegisters (i : Fin 3) : Fin 16 := i.castAdd 13
def emitCommand : Code := .call (ProgramLinking.liftProgram
  Squarefree.Program.prependRecordProgram emitRegisters emitMap)

theorem emit_run (s : Store) (key coeff : List Bool)
    (hk : s 222=key.reverse) (hc : s 228=coeff.reverse) :
    ExecutesIn emitCommand (4*key.length+4*coeff.length+13) s
      (Function.update (Function.update (Function.update s 222 []) 228 [])
        217 (Encoding.frame key++Encoding.frame coeff++s 217)) := by
  intro regs
  obtain ⟨rf,ht⟩ := Squarefree.Program.prependRecord_trace (regs ∘ emitRegisters)
    key coeff (s 217)
  have hin : projectState emitRegisters emitMap (⟨regs,s⟩ : Data) =
      Squarefree.Program.prependData (regs ∘ emitRegisters) key.reverse coeff.reverse (s 217) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [emitMap,hk,hc]
  rw [← hin] at ht
  have he := eval_call_from_state Squarefree.Program.prependRecordProgram
    emitRegisters emitMap (⟨regs,s⟩ : Data)
    (Fin.castAdd_injective 3 13) (by decide) ht
  let out := Function.update (Function.update (Function.update s 222 []) 228 [])
    217 (Encoding.frame key++Encoding.frame coeff++s 217)
  let rr := Function.extend emitRegisters rf regs
  have hout : embedState emitRegisters emitMap (⟨regs,s⟩ : Data)
      (Squarefree.Program.prependData rf [] []
        (Encoding.frame key++Encoding.frame coeff++s 217)) = (⟨rr,out⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 3 13) (by decide)
    · intro i
      exact (Fin.castAdd_injective 3 13).extend_apply rf regs i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [out,emitMap,Squarefree.Program.prependData]
    · intro i hi
      have h222 : i≠222 := by intro h; subst i; exact hi ⟨0,rfl⟩
      have h228 : i≠228 := by intro h; subst i; exact hi ⟨1,rfl⟩
      have h217 : i≠217 := by intro h; subst i; exact hi ⟨2,rfl⟩
      simp [out,h222,h228,h217]
  rw [hout] at he
  exact ⟨_,rr,le_rfl,he⟩

def increment : Code := Subexp.TupleProgram.pushConst 221 0 true

theorem increment_run (s : Store) : ExecutesIn increment 2 s
    (Function.update s 221 (true::s 221)) := by
  intro regs
  refine ⟨2,Function.update regs 0 true,le_rfl,?_⟩
  simpa [increment,Subexp.TupleProgram.pushedState] using
    Subexp.TupleProgram.pushConst_eval (221 : Fin 256) (0 : Fin 16) true (⟨regs,s⟩ : Data)

def step : Code := .seq readCoefficient (.seq keyCommand (.seq emitCommand increment))
def stepBudget (j n W : ℕ) : ℕ := 27*W+20*(j+n)+81

/-- Each iteration consumes one actual coefficient and restores all temporary
cells except the incremented unary exponent; beta and all other masters stay. -/
theorem step_run (s : Store) (mask bits rest : List Bool) (j : ℕ)
    (hs : s 240=bits++rest) (hw : (s 211).length=bits.length)
    (hm : s 214=mask) (hj : s 221=List.replicate j true)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[])
    (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn step (stepBudget j mask.length bits.length) s
      (Function.update (Function.update (Function.update s 240 rest)
        217 (record mask j bits++s 217)) 221 (List.replicate (j+1) true)) := by
  let s1 := Function.update (Function.update s 240 rest) 228 bits.reverse
  let s2 := Function.update s1 222 (keyBits mask j).reverse
  let s3 := Function.update (Function.update (Function.update s2 222 []) 228 [])
    217 (record mask j bits++s 217)
  have h1 := read_run s bits rest hs hw h226 h227 h228
  have h2 : ExecutesIn keyCommand (16*(j+mask.length)+40) s1 s2 :=
    key_run s1 mask j (by simp [s1,hm]) (by simp [s1,hj])
      (by simp [s1,h120]) (by simp [s1,h222]) (by simp [s1,h223]) (by simp [s1,h224])
  have h3 : ExecutesIn emitCommand (4*(keyBits mask j).length+4*bits.length+13) s2 s3 := by
    simpa [s3,s2,s1,record,List.append_assoc] using emit_run s2 (keyBits mask j) bits
      (by simp [s2]) (by simp [s2,s1])
  have h4 := increment_run s3
  have hout : Function.update s3 221 (true::s3 221) =
      Function.update (Function.update (Function.update s 240 rest)
        217 (record mask j bits++s 217)) 221 (List.replicate (j+1) true) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h228' : i=228 <;>
      by_cases h222' : i=222 <;> by_cases h217 : i=217 <;> by_cases h221 : i=221 <;>
      simp [s3,s2,s1,h240,h228',h222',h217,h221,h228,h222,hj,
        List.replicate_succ]
  rw [hout] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1
  all_goals first
    | rfl
    | (simp [stepBudget, keyBits, PerturbationProgram.Key.bits]; ring)

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- Exact order of the raw native accumulator: later degrees are prepended.
This deliberately retains zero coefficients; normalization is a separate job. -/
def emitted (mask : List Bool) : ℕ → List (List Bool) → List Bool → List Bool
  | _, [], acc => acc
  | j, c::cs, acc => emitted mask (j+1) cs (record mask j c++acc)

def array (cs : List (List Bool)) : List Bool := cs.flatten

def ready (base : Store) (j : ℕ) (cs : List (List Bool))
    (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base
    240 (array cs)) 217 acc) 221 (List.replicate j true)) 225 count

def loopPorts : UnaryForPrograms.Ports 16 256 := ⟨225,0,1⟩
def loop : Code := UnaryForPrograms.forCmd loopPorts step

def loopBudget (j n W N : ℕ) : ℕ := N*(stepBudget (j+N) n W+2)+2

theorem popped_ready (base : Store) (j : ℕ) (cs : List (List Bool))
    (acc count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped loopPorts (⟨regs,ready base j cs acc count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?,ready base j cs acc count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,loopPorts,ready]
  · simp [UnaryForPrograms.popped,loopPorts,ready]

theorem loop_visits (base : Store) (mask : List Bool) (W : ℕ)
    (hw : (base 211).length=W) (hm : base 214=mask)
    (h120 : base 120=[]) (h222 : base 222=[]) (h223 : base 223=[])
    (h224 : base 224=[]) (h226 : base 226=[]) (h227 : base 227=[]) (h228 : base 228=[])
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (j : ℕ) (acc count : List Bool) (hlen : count.length=cs.length)
    (regs : Fin 16 → Bool) :
    ∃ costs n rf, UnaryForPrograms.Visits loopPorts step costs n
      (⟨regs,ready base j cs acc count⟩ : Data)
      (⟨rf,ready base (j+cs.length) [] (emitted mask j cs acc) []⟩ : Data) ∧
      n ≤ loopBudget j mask.length W cs.length := by
  induction cs generalizing j acc count regs with
  | nil =>
      have hh : count=[] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[],2,readRegs regs 0 1 none,?_,by simp [loopBudget]⟩
      simpa [emitted,popped_ready] using
        UnaryForPrograms.Visits.done (p := loopPorts) (body := step)
          (⟨regs,ready base j [] acc []⟩ : Data) (by simp [ready,loopPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hc0 : c.length=W := hc c (by simp)
          have hct : ∀ d ∈ cs,d.length=W := fun d hd => hc d (by simp [hd])
          have hlen' : count.length=cs.length := by simpa using hlen
          let s := ready base j (c::cs) acc count
          have hs := step_run s mask c (array cs) j
            (by simp [s,ready,array]) (by simpa [s,ready] using hw.trans hc0.symm)
            (by simp [s,ready,hm]) (by simp [s,ready])
            (by simp [s,ready,h120]) (by simp [s,ready,h222])
            (by simp [s,ready,h223]) (by simp [s,ready,h224])
            (by simp [s,ready,h226]) (by simp [s,ready,h227]) (by simp [s,ready,h228])
          have hout : Function.update (Function.update (Function.update s 240 (array cs))
              217 (record mask j c++s 217)) 221 (List.replicate (j+1) true) =
              ready base (j+1) cs (record mask j c++acc) count := by
            funext i
            by_cases h240 : i=240 <;> by_cases h217 : i=217 <;>
              by_cases h221 : i=221 <;> by_cases h225 : i=225 <;>
              simp [s,ready,h240,h217,h221,h225]
          rw [hout,hc0] at hs
          obtain ⟨nb,rb,hnb,hb⟩ := hs (readRegs regs 0 1 (some bit))
          obtain ⟨costs,nt,rt,ht,hnt⟩ := ih hct (j+1) (record mask j c++acc) count hlen' rb
          refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
          · have hv := UnaryForPrograms.Visits.step
              (p := loopPorts) (body := step)
              (d := (⟨regs,ready base j (c::cs) acc (bit::count)⟩ : Data))
              (by simp [ready,loopPorts])
              (by simpa only [popped_ready,List.head?_cons,List.tail_cons] using hb)
              (by simp [ready,loopPorts,UnaryForPrograms.popped]) ht
            simpa [emitted,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv
          · simp only [loopBudget,stepBudget,List.length_cons] at *
            nlinarith

theorem loop_run (base : Store) (mask : List Bool) (W : ℕ)
    (hw : (base 211).length=W) (hm : base 214=mask)
    (h120 : base 120=[]) (h222 : base 222=[]) (h223 : base 223=[])
    (h224 : base 224=[]) (h226 : base 226=[]) (h227 : base 227=[]) (h228 : base 228=[])
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (j : ℕ) (acc count : List Bool) (hlen : count.length=cs.length) :
    ExecutesIn loop (loopBudget j mask.length W cs.length)
      (ready base j cs acc count)
      (ready base (j+cs.length) [] (emitted mask j cs acc) []) := by
  intro regs
  obtain ⟨costs,n,rf,ht,hn⟩ := loop_visits base mask W hw hm h120 h222 h223 h224
    h226 h227 h228 cs hc j acc count hlen regs
  exact ⟨n,rf,hn,ht.eval⟩

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- The first cell is the node value, not a positive-Z coefficient. -/
def dropConstant : Code := .seq (takeWord 211 226 227 240 228 0 1) (clear 228)

theorem dropConstant_run (s : Store) (bits rest : List Bool)
    (hs : s 240=bits++rest) (hw : (s 211).length=bits.length)
    (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn dropConstant (16*bits.length+14) s (Function.update s 240 rest) := by
  intro regs
  let mid := afterTake (⟨regs,s⟩ : Data) 240 228 0 1 bits rest
  have h1 := takeWord_eval (⟨regs,s⟩ : Data) 211 226 227 240 228 0 1
    (by decide) (by decide) bits rest hs h226 h227 hw
  obtain ⟨n,rf,hn,h2⟩ := clear_run 228 mid.stacks mid.regs
  have hout : Function.update mid.stacks 228 [] = Function.update s 240 rest := by
    simp [mid,afterTake,h228]
  rw [hout] at h2
  refine ⟨14*bits.length+11+n,rf,?_,h1.seq h2⟩
  simp [mid,afterTake,h228] at hn
  omega

def start : Code := .seq (copy 213 225) increment

theorem start_run (s : Store) (cs : List (List Bool))
    (hs : s 240=array cs) (hJ : s 213=List.replicate cs.length true)
    (h120 : s 120=[]) (h221 : s 221=[]) (h225 : s 225=[]) :
    ExecutesIn start (7*cs.length+7) s
      (ready s 1 cs (s 217) (List.replicate cs.length true)) := by
  let mid := Function.update s 225 (List.replicate cs.length true)
  have h1 : ExecutesIn (copy 213 225) (7*cs.length+5) s mid := by
    simpa [mid,hJ,h225] using copy_run 213 225 s (by decide) (by decide) (by decide) h120
  have h2 := increment_run mid
  have hout : Function.update mid 221 (true::mid 221) =
      ready s 1 cs (s 217) (List.replicate cs.length true) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h217 : i=217 <;>
      by_cases h221' : i=221 <;> by_cases h225' : i=225 <;>
      simp [mid,ready,h240,h217,h221',h225',h221,hs]
  rw [hout] at h2
  convert h1.seq h2 using 1 ; first | omega | rfl

def branch : Code := .ite 1 (.seq dropConstant loop) (.base .skip)
def command : Code := .seq start (.seq (UnaryForPrograms.popCmd loopPorts)
  (.seq branch (clear 221)))

def budget (J n W : ℕ) : ℕ := 9*J+16*W+loopBudget 1 n W J+29

private theorem loopBudget_mono (j n W a b : ℕ) (h : a ≤ b) :
    loopBudget j n W a ≤ loopBudget j n W b := by
  unfold loopBudget
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul h
  unfold stepBudget
  omega

theorem branch_run (s : Store) (mask : List Bool) (W : ℕ)
    (hw : (s 211).length=W) (hm : s 214=mask)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (h224 : s 224=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[])
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W) (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 16*W+loopBudget 1 mask.length W cs.tail.length+15 ∧
      Eval branch n
        (⟨readRegs regs 0 1 (List.replicate cs.length true).head?,
          ready s 1 cs (s 217) (List.replicate cs.length true).tail⟩ : Data)
        (⟨rf,ready s (1+cs.tail.length) [] (emitted mask 1 cs.tail (s 217)) []⟩ : Data) := by
  cases cs with
  | nil =>
      refine ⟨1,readRegs regs 0 1 none,?_,?_⟩
      · unfold loopBudget; omega
      · simpa [branch,emitted] using
          Eval.ite_false (test := (1:Fin 16)) (yes := .seq dropConstant loop)
            (by simp : (readRegs regs 0 1 none) 1=false)
            (Eval.base (StructuredProgram.Eval.skip
              (⟨readRegs regs 0 1 none,ready s 1 [] (s 217) []⟩ : Data)))
  | cons c cs =>
      have hc0 := hc c (by simp)
      let a := ready s 1 (c::cs) (s 217) (List.replicate cs.length true)
      have hd := dropConstant_run a c (array cs)
        (by simp [a,ready,array]) (by simpa [a,ready] using hw.trans hc0.symm)
        (by simp [a,ready,h226]) (by simp [a,ready,h227]) (by simp [a,ready,h228])
      have ha : Function.update a 240 (array cs) =
          ready s 1 cs (s 217) (List.replicate cs.length true) := by
        funext i
        by_cases h240 : i=240 <;> simp [a,ready,Function.update_apply,h240]
      rw [ha,hc0] at hd
      have hl := loop_run s mask W hw hm h120 h222 h223 h224 h226 h227 h228
        cs (fun x hx => hc x (by simp [hx])) 1 (s 217) (List.replicate cs.length true)
        (by simp)
      obtain ⟨n,rf,hn,he⟩ := hd.seq hl (readRegs regs 0 1 (some true))
      refine ⟨n+1,rf,by simp only [List.tail_cons]; omega,?_⟩
      simpa [branch,a,List.replicate_succ] using
        Eval.ite_true (test := (1:Fin 16)) (no := .base .skip)
          (by simp : (readRegs regs 0 1 (some true)) 1=true) he

/-- Complete fixed-control array-to-dictionary producer. All scratch and the
consumed source are cleared; every other input stack is literally preserved. -/
theorem command_run (s : Store) (mask : List Bool) (W : ℕ)
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (hs : s 240=array cs) (hJ : s 213=List.replicate cs.length true)
    (hw : (s 211).length=W) (hm : s 214=mask)
    (h120 : s 120=[]) (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (h224 : s 224=[]) (h225 : s 225=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn command (budget cs.length mask.length W) s
      (Function.update (Function.update s 240 []) 217 (emitted mask 1 cs.tail (s 217))) := by
  intro regs
  obtain ⟨n1,r1,hn1,h1⟩ := start_run s cs hs hJ h120 h221 h225 regs
  have hp := UnaryForPrograms.pop_eval loopPorts
    (⟨r1,ready s 1 cs (s 217) (List.replicate cs.length true)⟩ : Data)
  rw [popped_ready] at hp
  obtain ⟨n2,r2,hn2,h2⟩ := branch_run s mask W hw hm h120 h222 h223 h224 h226 h227 h228 cs hc r1
  let last := ready s (1+cs.tail.length) [] (emitted mask 1 cs.tail (s 217)) []
  obtain ⟨n3,r3,hn3,h3⟩ := clear_run 221 last r2
  have hout : Function.update last 221 [] =
      Function.update (Function.update s 240 []) 217 (emitted mask 1 cs.tail (s 217)) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h217 : i=217 <;>
      by_cases h221' : i=221 <;> by_cases h225' : i=225 <;>
      simp [last,ready,array,h240,h217,h221',h225',h221,h225]
  rw [hout] at h3
  refine ⟨n1+(1+(n2+n3)),r3,?_,h1.seq (hp.seq (h2.seq h3))⟩
  have htail : cs.tail.length ≤ cs.length := by cases cs <;> simp
  have hm := loopBudget_mono 1 mask.length W cs.tail.length cs.length htail
  simp [last,ready] at hn3
  unfold budget
  omega

theorem budget_polynomial (J n W : ℕ) :
    budget J n W ≤ 150*(J+1)*(J+n+W+1) := by
  unfold budget loopBudget stepBudget
  ring_nf
  omega

def program := compiled command 240 217

theorem program_run (s : Store) (mask : List Bool) (W : ℕ)
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (hs : s 240=array cs) (hJ : s 213=List.replicate cs.length true)
    (hw : (s 211).length=W) (hm : s 214=mask)
    (h120 : s 120=[]) (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (h224 : s 224=[]) (h225 : s 225=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[])
    (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn program (budget cs.length mask.length W+1)
      ((⟨regs,s⟩ : Data).withPC (some program.entry))
      ((⟨rf,Function.update (Function.update s 240 [])
        217 (emitted mask 1 cs.tail (s 217))⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_run s mask W cs hc hs hJ hw hm
    h120 h221 h222 h223 h224 h225 h226 h227 h228 regs
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 240 217⟩

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

/-- Exact mathematical record list, before the native prepend reversal. -/
def entries {n d B : ℕ} (v : Fin n) :
    ℕ → List (Coefficient d B) → List (Index (Fin n) × Coefficient d B)
  | _, [] => []
  | j, c::cs => (⟨0,j,{v}⟩,c)::entries v (j+1) cs

@[simp] theorem entries_length {n d B : ℕ} (v : Fin n) (j : ℕ)
    (cs : List (Coefficient d B)) : (entries v j cs).length=cs.length := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp [entries,ih]

@[simp] theorem record_typed {n d B : ℕ} (v : Fin n) (j : ℕ) (c : Coefficient d B) :
    record (encodeMask {v}) j (RingProgram.flat c) =
      Encoding.frame (encodeIndex (⟨0,j,{v}⟩ : Index (Fin n))) ++
        Encoding.frame (RingProgram.flat c) := by
  simp [record,keyBits,PerturbationProgram.Key.bits,encodeIndex,Encoding.encodeNat,
    List.append_assoc]

@[simp] theorem dictionaryBits_append {n d B : ℕ}
    (p q : List (Index (Fin n) × Coefficient d B)) :
    dictionaryBits (p++q)=dictionaryBits p++dictionaryBits q := by
  simp [dictionaryBits,List.flatMap_append]

theorem emitted_typed {n d B : ℕ} (v : Fin n) (j : ℕ)
    (cs : List (Coefficient d B)) (acc : List (Index (Fin n) × Coefficient d B)) :
    emitted (encodeMask {v}) j (cs.map RingProgram.flat) (dictionaryBits acc) =
      dictionaryBits ((entries v j cs).reverse++acc) := by
  induction cs generalizing j acc with
  | nil => simp [emitted,entries]
  | cons c cs ih =>
      simp only [List.map_cons,emitted,record_typed]
      rw [show Encoding.frame (encodeIndex (⟨0,j,{v}⟩ : Index (Fin n))) ++
          Encoding.frame (RingProgram.flat c) ++ dictionaryBits acc =
          dictionaryBits ((⟨0,j,{v}⟩,c)::acc) by rw [dictionaryBits_cons]]
      rw [ih]
      simp [entries,List.reverse_cons,List.append_assoc]

theorem entries_eq_emitPositive {n d B : ℕ} (v : Fin n) (J j : ℕ)
    (cs : List (Coefficient d B)) (h : j+cs.length < J) :
    entries v (j+1) cs=emitPositive v J j cs := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih =>
      have hfirst : j+1 < J := by simp only [List.length_cons] at h; omega
      have hnext : j+1+cs.length < J := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      simp only [entries,emitPositive,ite_eq_left hfirst]
      rw [ih (j+1) hnext]
      rfl

/-- The runtime loop emits exactly the previously specified positive-Z list,
with only the documented prepend reversal. It never emits the constant cell. -/
theorem full_array_output {n d B : ℕ} (v : Fin n)
    (cs : List (Coefficient d B)) (acc : List (Index (Fin n) × Coefficient d B)) :
    emitted (encodeMask {v}) 1 (cs.map RingProgram.flat).tail (dictionaryBits acc) =
      dictionaryBits ((emitPositive v cs.length 0 cs.tail).reverse++acc) := by
  rw [← List.map_tail,emitted_typed]
  cases cs with
  | nil => rfl
  | cons c cs =>
      change dictionaryBits ((entries v (0+1) cs).reverse++acc) = _
      rw [entries_eq_emitPositive v (c::cs).length 0 cs (by simp)]
      rfl

/-- Closed typed producer contract for the exact input/output array ABI. -/
theorem coefficientArray_run {n d B : ℕ} (s : Store) (v : Fin n)
    (cs : List (Coefficient d B)) (acc : List (Index (Fin n) × Coefficient d B))
    (hs : s 240=coefficientArray cs) (hJ : s 213=List.replicate cs.length true)
    (hw : (s 211).length=d*B) (hm : s 214=encodeMask {v})
    (ha : s 217=dictionaryBits acc)
    (h120 : s 120=[]) (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (h224 : s 224=[]) (h225 : s 225=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn command (budget cs.length n (d*B)) s
      (Function.update (Function.update s 240 []) 217
        (dictionaryBits ((emitPositive v cs.length 0 cs.tail).reverse++acc))) := by
  have hc : ∀ c ∈ cs.map RingProgram.flat,c.length=d*B := by
    intro c hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    exact RingProgram.flat_length x
  have he := command_run s (encodeMask {v}) (d*B) (cs.map RingProgram.flat) hc
    (by simpa [array,coefficientArray] using hs) (by simpa using hJ) hw hm
    h120 h221 h222 h223 h224 h225 h226 h227 h228
  simpa only [List.length_map,encodeMask_length,ha,full_array_output] using he

/-- Uniform bit-program transition bound, including the compiled return instruction. -/
theorem compiled_budget_polynomial (J n W : ℕ) :
    budget J n W+1 ≤ 151*(J+1)*(J+n+W+1) := by
  have h := budget_polynomial J n W
  nlinarith

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram

end OAI.Algorithms
