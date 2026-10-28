import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarCacheFlat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPower
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

abbrev Data := State 8 24

def state (regs : Fin 8 → Bool) (a r width la lr lw p n power counter : List Bool) : Data :=
  ⟨regs,![p,n,power,[],[],[],[],[],[],[],[],[],[],[],[],[],[],la,lr,lw,a,r,width,counter]⟩

abbrev copy (src dst : Fin 24) : Cmd 8 24 := .call (StackRoutines.copyProgram src dst 3 0 1)
abbrev copies : Cmd 8 24 := .seq (copy 20 17) (.seq (copy 21 18) (copy 22 19))
def flatPorts : Fin 20 → Fin 24 := Fin.castAdd 4
abbrev flat : Cmd 8 24 := .call (ProgramLinking.liftProgram hFlatProgram id flatPorts)
def powerRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def powerPorts : Fin 2 → Fin 24 := ![23,2]
abbrev powerCall : Cmd 8 24 := .call (ProgramLinking.liftProgram powerProgram powerRegs powerPorts)
abbrev popCounter : Cmd 8 24 := .base (.atom (.pop 23 0 1))
abbrev makePower : Cmd 8 24 := .seq (copy 21 23) (.seq popCounter powerCall)
abbrev command : Cmd 8 24 := .seq copies (.seq flat makePower)
def program := compiled command 20 0

def denominatorWord (R : ℕ) : List Bool := List.replicate (R-1) false ++ [true]

private theorem flatPorts_inj : Function.Injective flatPorts := Fin.castAdd_injective _ _
private theorem powerRegs_inj : Function.Injective powerRegs := Fin.castAdd_injective _ _
private theorem powerPorts_inj : Function.Injective powerPorts := by decide

theorem copies_eval (regs : Fin 8 → Bool) (a r width : List Bool) :
    ∃ rf, Eval copies (7*(a.length+r.length+width.length)+15)
      (state regs a r width [] [] [] [] [] [] [])
      (state rf a r width a r width [] [] [] []) := by
  let s := state regs a r width [] [] [] [] [] [] []
  let s1 := SubexpScanPrimitives.afterCopy s 20 17 0 1
  let s2 := SubexpScanPrimitives.afterCopy s1 21 18 0 1
  let s3 := SubexpScanPrimitives.afterCopy s2 22 19 0 1
  have h1 := SubexpScanPrimitives.copy_eval s 20 17 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 := SubexpScanPrimitives.copy_eval s1 21 18 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks])
  have h3 := SubexpScanPrimitives.copy_eval s2 22 19 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks])
  have hs : s3 = state s3.regs a r width a r width [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  have h := h1.seq (h2.seq h3)
  change Eval copies _ s s3 at h
  rw [hs] at h
  refine ⟨s3.regs,?_⟩
  convert h using 1 ; simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] ; omega

def flatCost (A R W : ℕ) : ℕ :=
  12*R+400*(A+1)*(R+1)*(2*A*R+5)+110*(R+1)*(W+(1+2*A*R)+4)+16

theorem flat_eval (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ t ≤ flatCost a.length r.length width.length, ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
      Eval flat t (state regs a r width a r width [] [] [] [])
        (state rf a r width [] [] width words.flatten
          (List.replicate (r.length*width.length) false) [] []) ∧
      words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  obtain ⟨rf,words,⟨t,ht,he⟩,hlen,hwidth,hvalues⟩ := hFlatProgram_runsIn regs a r width hw
  let start := state regs a r width a r width [] [] [] []
  have hp : projectState id flatPorts start = LayoutBinomialProgram.finalState regs a r width [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [start,state,flatPorts]
  have h := eval_call_from_state hFlatProgram id flatPorts start Function.injective_id flatPorts_inj
    (by rw [hp]; exact he)
  have ho : embedState id flatPorts start
      (LayoutBinomialProgram.finalState rf [] [] width [] words.flatten
        (List.replicate (r.length*width.length) false)) =
      state rf a r width [] [] width words.flatten
        (List.replicate (r.length*width.length) false) [] [] := by
    apply embedState_eq_of_ports id flatPorts _ _ _ Function.injective_id flatPorts_inj
    · intro j; rfl
    · intro j hj; exact (hj ⟨j,rfl⟩).elim
    · intro j; fin_cases j <;> simp [state,flatPorts,LayoutBinomialProgram.finalState]
    · intro j hj
      have hlow : 20 ≤ j.val := by
        by_contra hn
        have hjlt : j.val < 20 := by omega
        exact hj ⟨⟨j.val,hjlt⟩,Fin.ext rfl⟩
      fin_cases j <;> simp_all [start,state]
  rw [ho] at h
  exact ⟨t,ht,rf,words,h,hlen,hwidth,hvalues⟩

theorem makePower_eval (regs : Fin 8 → Bool) (a r width p n : List Bool) :
    ∃ rf, Eval makePower (7*r.length+4*(r.length-1)+11)
      (state regs a r width [] [] width p n [] [])
      (state rf a r width [] [] width p n (denominatorWord r.length) []) := by
  let s := state regs a r width [] [] width p n [] []
  let s1 := SubexpScanPrimitives.afterCopy s 21 23 0 1
  let s2 : Data := ⟨readRegs s1.regs 0 1 r.head?,Function.update s1.stacks 23 r.tail⟩
  have h1 := SubexpScanPrimitives.copy_eval s 21 23 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 : Eval popCounter 1 s1 s2 := by
    convert (Eval.base (StructuredProgram.Eval.atom (.pop (23:Fin 24) (0:Fin 8) 1) s1)) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,
StructuredProgram.Atom.instr,
execInstr]
    · funext j
      fin_cases j <;> simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,
StructuredProgram.Atom.instr,
execInstr]
  have hp : projectState powerRegs powerPorts s2 = powerState (s2.regs ∘ powerRegs) r.tail [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [powerPorts,s2,s1,s,state,
      SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  have ht := compiled_halt_trace (powerCommand_eval (s2.regs ∘ powerRegs) r.tail []) 0 1
  have h3 := eval_call_from_state powerProgram powerRegs powerPorts s2 powerRegs_inj powerPorts_inj
    (by rw [hp]; exact ht)
  let target := embedState powerRegs powerPorts s2
    (powerState (readRegs (s2.regs ∘ powerRegs) 0 1 none) []
      (List.replicate r.tail.length false ++ [true]))
  have he : target = state target.regs a r width [] [] width p n (denominatorWord r.length) [] := by
    apply embedState_eq_of_ports powerRegs powerPorts _ _ _ powerRegs_inj powerPorts_inj
    · intro j; exact embedState_register powerRegs powerPorts s2 _ powerRegs_inj j
    · intro j hj; exact embedState_register_frame powerRegs powerPorts s2 _ j hj
    · intro j; fin_cases j <;> simp [state,powerPorts,powerState,denominatorWord]
    · intro j hj
      have hneq : j≠23 ∧ j≠2 := by
        constructor
        · intro h; exact hj ⟨0,h.symm⟩
        · intro h; exact hj ⟨1,h.symm⟩
      fin_cases j <;> simp_all [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  change Eval powerCall _ s2 target at h3
  rw [he] at h3
  refine ⟨target.regs,?_⟩
  have h := h1.seq (h2.seq h3)
  convert h using 1 ; simp [s,state,List.length_tail] ; omega

/-- No coefficient list or denominator word is an input. Their full setup is
charged, while the three runtime unary parameters remain available. -/
theorem program_runsIn (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn program
        (7*(a.length+r.length+width.length)+flatCost a.length r.length width.length+11*r.length+27)
        ((state regs a r width [] [] [] [] [] [] []).withPC (some program.entry))
        ((state rf a r width [] [] width words.flatten
          (List.replicate (r.length*width.length) false) (denominatorWord r.length) []).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (denominatorWord r.length)=2^(r.length-1) := by
  obtain ⟨r1,h1⟩ := copies_eval regs a r width
  obtain ⟨t,ht,r2,words,h2,hlen,hwidth,hvalues⟩ := flat_eval r1 a r width hw
  obtain ⟨r3,h3⟩ := makePower_eval r2 a r width words.flatten
    (List.replicate (r.length*width.length) false)
  refine ⟨r3,words,⟨_,?_,compiled_halt_trace (h1.seq (h2.seq h3)) 20 0⟩,
    hlen,hwidth,hvalues,powerWord_value _⟩
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
