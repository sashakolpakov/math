import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWordLiftMachine
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Four-word streaming lift from the residue field

The source modulus is stack 5. Stack 8 contains the four source words and
receives the four lifted words. Source and target width shapes on stacks 10
and 11 are preserved. All other local work stacks are cleared on return.
-/

namespace SubexponentialSAT.SubexpFlatLift

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def stackArray (out modulus raw shape flat packed sourceWidth targetWidth counter tmp : List Bool)
    (frame : Fin 6 → List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (m := 14) (n := 6) (motive := fun _ => List Bool)
    (![out,[],[],[],[],modulus,raw,shape,flat,packed,sourceWidth,targetWidth,counter,tmp] :
      Fin 14 → List Bool) frame i

def state (regs : Fin 8 → Bool)
    (out modulus raw shape flat packed sourceWidth targetWidth counter tmp : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, stackArray out modulus raw shape flat packed sourceWidth targetWidth counter tmp frame⟩

def ready (regs : Fin 8 → Bool) (modulus flat packed sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  state regs [] modulus [] [] flat packed sourceWidth targetWidth [] [] frame

private theorem scalar_stack_updates
    (out modulus raw shape flat packed sourceWidth targetWidth counter tmp : List Bool)
    (frame : Fin 6 → List Bool) :
    stackArray out modulus raw shape flat packed sourceWidth targetWidth counter tmp frame =
      Function.update (Function.update (Function.update
        (stackArray [] modulus [] [] flat packed sourceWidth targetWidth counter tmp frame)
        0 out) 6 raw) 7 shape := by
  funext i
  fin_cases i <;> rfl

private theorem scalar_stack_frame
    (out raw shape out' raw' shape' modulus flat packed sourceWidth targetWidth counter tmp : List Bool)
    (frame : Fin 6 → List Bool) (i : Fin 20)
    (h0 : i ≠ 0) (h6 : i ≠ 6) (h7 : i ≠ 7) :
    stackArray out modulus raw shape flat packed sourceWidth targetWidth counter tmp frame i =
      stackArray out' modulus raw' shape' flat packed sourceWidth targetWidth counter tmp frame i := by
  have hleft := congrFun
    (scalar_stack_updates out modulus raw shape flat packed sourceWidth targetWidth counter tmp frame) i
  have hright := congrFun
    (scalar_stack_updates out' modulus raw' shape' flat packed sourceWidth targetWidth counter tmp frame) i
  simp only [Function.update_apply, h0, h6, h7, ite_false] at hleft hright
  exact hleft.trans hright.symm

private theorem take_word_state (regs : Fin 8 → Bool)
    (x modulus flat packed sourceWidth targetWidth : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (ready regs modulus (x ++ flat) packed sourceWidth targetWidth frame)
        8 6 0 1 x flat =
      state (readRegs regs 0 1 none) [] modulus x [] flat packed
        sourceWidth targetWidth [] [] frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTake, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]

private theorem copy_width_state (regs : Fin 8 → Bool)
    (x modulus flat packed sourceWidth targetWidth : List Bool) (frame : Fin 6 → List Bool) :
    afterCopy (state regs [] modulus x [] flat packed sourceWidth targetWidth [] [] frame)
        11 7 0 1 =
      state (readRegs regs 0 1 none) [] modulus x targetWidth flat packed
        sourceWidth targetWidth [] [] frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterCopy, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.copyStacks]

private theorem transfer_word_state (regs : Fin 8 → Bool)
    (output modulus flat packed sourceWidth targetWidth : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (state regs output modulus [] [] flat packed sourceWidth targetWidth [] [] frame)
        0 9 0 1 =
      ready (readRegs regs 0 1 none) modulus flat (output.reverse ++ packed)
        sourceWidth targetWidth frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTransfer, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.transferStacks]

private theorem transfer_packed_state (regs : Fin 8 → Bool)
    (output modulus sourceWidth targetWidth : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (ready regs modulus [] output.reverse sourceWidth targetWidth frame) 9 8 0 1 =
      ready (readRegs regs 0 1 none) modulus output [] sourceWidth targetWidth frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTransfer, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.transferStacks]

def scalarPorts : Fin 8 → Fin 20 := Fin.castAdd 12

theorem scalarPorts_injective : Function.Injective scalarPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 20 => x.val) h

abbrev scalarLift : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram SubexpWordLiftMachine.program id scalarPorts)

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

theorem scalarLift_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (x : Word (baseWidth p 1)) (flat packed sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool) (hwidth : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ SubexpWordLiftMachine.runtimeBound (baseWidth p 1) (baseWidth p μ) M.bits.length,
      ∃ regs', Eval scalarLift n
        (state regs [] M.bits x.val targetWidth flat packed sourceWidth targetWidth [] [] frame)
        (state regs' (SubexpWordLift.liftWordRun p μ M x).1.val M.bits [] []
          flat packed sourceWidth targetWidth [] [] frame) := by
  obtain ⟨rf,n,hn,ht⟩ := SubexpWordLiftMachine.run p μ M hμ regs x targetWidth hwidth
  let a : State 8 8 := ⟨regs, ModularRingPrograms.extendSeven
    (ModularDivisionPrograms.resting [] M.bits x.val) targetWidth⟩
  let b : State 8 8 := ⟨rf, ModularRingPrograms.extendSeven
    (ModularDivisionPrograms.resting (SubexpWordLift.liftWordRun p μ M x).1.val M.bits []) []⟩
  let d := state regs [] M.bits x.val targetWidth flat packed sourceWidth targetWidth [] [] frame
  have ha : embedState id scalarPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intros; rfl
  have hb : embedState id scalarPorts d b =
      state rf (SubexpWordLift.liftWordRun p μ M x).1.val M.bits [] []
        flat packed sourceWidth targetWidth [] [] frame := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      have h0 : j ≠ 0 := by
        intro h; subst j; exact hj ⟨0,rfl⟩
      have h6 : j ≠ 6 := by
        intro h; subst j; exact hj ⟨6,rfl⟩
      have h7 : j ≠ 7 := by
        intro h; subst j; exact hj ⟨7,rfl⟩
      exact scalar_stack_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ j h0 h6 h7
  have h := eval_call_lifted SubexpWordLiftMachine.program id scalarPorts d
    Function.injective_id scalarPorts_injective (a := a) (b := b) ht
  exact ⟨n,hn,rf,by simpa only [scalarLift,ha,hb] using h⟩

abbrev liftOne : Cmd 8 20 :=
  .seq (takeWord 10 12 13 8 6 0 1)
    (.seq (.call (StackRoutines.copyProgram 11 7 13 (0 : Fin 8) 1))
      (.seq scalarLift (.call (StackRoutines.transferProgram 0 9 (0 : Fin 8) 1))))

def wordCost (b B m : ℕ) : ℕ :=
  SubexpWordLiftMachine.runtimeBound b B m + 14*b + 10*B + 19

theorem liftOne_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (x : Word (baseWidth p 1)) (flat packed sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length, ∃ regs',
      Eval liftOne n
        (ready regs M.bits (x.val++flat) packed sourceWidth targetWidth frame)
        (ready regs' M.bits flat
          ((SubexpWordLift.liftWordRun p μ M x).1.val.reverse++packed)
          sourceWidth targetWidth frame) := by
  let r₁ := readRegs regs 0 1 none
  let d₀ := ready regs M.bits (x.val++flat) packed sourceWidth targetWidth frame
  let d₁ := state r₁ [] M.bits x.val [] flat packed sourceWidth targetWidth [] [] frame
  have h₁ : Eval (takeWord 10 12 13 8 6 0 1) (14*baseWidth p 1+11) d₀ d₁ := by
    have h := takeWord_eval d₀ 10 12 13 8 6 0 1 (by decide) (by decide)
      x.val flat rfl rfl rfl (hb.trans x.property.symm)
    have he : afterTake d₀ 8 6 0 1 x.val flat = d₁ :=
      take_word_state regs x.val M.bits flat packed sourceWidth targetWidth frame
    simpa only [x.property,he] using h
  let d₂ := state r₁ [] M.bits x.val targetWidth flat packed sourceWidth targetWidth [] [] frame
  have h₂ : Eval (.call (StackRoutines.copyProgram 11 7 13 (0 : Fin 8) 1))
      (7*baseWidth p μ+5) d₁ d₂ := by
    have h := copy_eval d₁ 11 7 13 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    have he : afterCopy d₁ 11 7 0 1 = d₂ := by
      simpa only [d₁,d₂,r₁,StackRoutines.readRegs_reset] using
        copy_width_state r₁ x.val M.bits flat packed sourceWidth targetWidth frame
    have hl : (d₁.stacks 11).length = baseWidth p μ := hB
    simpa only [he,hl] using h
  obtain ⟨n,hn,r₂,h₃⟩ := scalarLift_eval p μ M hμ r₁ x flat packed sourceWidth targetWidth frame hB
  let y := (SubexpWordLift.liftWordRun p μ M x).1
  let d₃ := state r₂ y.val M.bits [] [] flat packed sourceWidth targetWidth [] [] frame
  have h₄ : Eval (.call (StackRoutines.transferProgram 0 9 (0 : Fin 8) 1))
      (3*baseWidth p μ+3) d₃
      (ready (readRegs r₂ 0 1 none) M.bits flat (y.val.reverse++packed)
        sourceWidth targetWidth frame) := by
    have h := transfer_eval d₃ 0 9 0 1 (by decide) (by decide)
    have he : afterTransfer d₃ 0 9 0 1 =
        ready (readRegs r₂ 0 1 none) M.bits flat (y.val.reverse++packed)
          sourceWidth targetWidth frame :=
      transfer_word_state r₂ y.val M.bits flat packed sourceWidth targetWidth frame
    have hl : (d₃.stacks 0).length = baseWidth p μ := y.property
    simpa only [he,hl] using h
  refine ⟨(14*baseWidth p 1+11)+(7*baseWidth p μ+5+(n+(3*baseWidth p μ+3))),
    ?_,readRegs r₂ 0 1 none,Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))⟩
  unfold wordCost
  omega

def repeatLift : ℕ → Cmd 8 20
  | 0 => .base .skip
  | n+1 => .seq liftOne (repeatLift n)

def flatten {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

def liftedWords (xs : List (Word (baseWidth p 1))) : List (Word (baseWidth p μ)) :=
  xs.map (fun x => (SubexpWordLift.liftWordRun p μ M x).1)

theorem repeatLift_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (xs : List (Word (baseWidth p 1))) (packed sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ xs.length * wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length, ∃ regs',
      Eval (repeatLift xs.length) n
        (ready regs M.bits (flatten xs) packed sourceWidth targetWidth frame)
        (ready regs' M.bits [] ((flatten (liftedWords p μ M xs)).reverse++packed)
          sourceWidth targetWidth frame) := by
  induction xs generalizing regs packed with
  | nil =>
      exact ⟨0,by simp,regs,by simpa [repeatLift,flatten,liftedWords] using
        (Eval.base (StructuredProgram.Eval.skip
          (ready regs M.bits [] packed sourceWidth targetWidth frame)))⟩
  | cons x xs ih =>
      obtain ⟨n,hn,r₁,h₁⟩ := liftOne_eval p μ M hμ regs x (flatten xs) packed
        sourceWidth targetWidth frame hb hB
      obtain ⟨m,hm,r₂,h₂⟩ := ih (regs := r₁)
        (packed := (SubexpWordLift.liftWordRun p μ M x).1.val.reverse++packed)
      refine ⟨n+m,?_,r₂,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · simpa [repeatLift,flatten,liftedWords,List.reverse_append,List.append_assoc] using
          Eval.seq h₁ h₂

abbrev coefficientLift : Cmd 8 20 :=
  .seq (repeatLift 4) (.call (StackRoutines.transferProgram 9 8 (0 : Fin 8) 1))

def quadWords {B : ℕ} (a : Quad (Word B)) : List (Word B) := [a.c0,a.c1,a.c2,a.c3]
def encode {B : ℕ} (a : Quad (Word B)) : List Bool := flatten (quadWords a)

@[simp] theorem encode_length {B : ℕ} (a : Quad (Word B)) : (encode a).length = 4*B := by
  simp [encode,quadWords,flatten,a.c0.property,a.c1.property,a.c2.property,a.c3.property]
  omega

theorem coefficientLift_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (a : Quad (Word (baseWidth p 1))) (sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ 4*wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length+12*baseWidth p μ+3,
      ∃ regs', Eval coefficientLift n
        (ready regs M.bits (encode a) [] sourceWidth targetWidth frame)
        (ready regs' M.bits (encode (SubexpWordLift.liftQuadRun p μ M a).1) []
          sourceWidth targetWidth frame) := by
  have he : liftedWords p μ M (quadWords a) =
      quadWords (SubexpWordLift.liftQuadRun p μ M a).1 := rfl
  obtain ⟨n,hn,r₁,h₁⟩ := repeatLift_eval p μ M hμ regs (quadWords a) []
    sourceWidth targetWidth frame hb hB
  simp only [he,List.append_nil] at h₁
  let result := (SubexpWordLift.liftQuadRun p μ M a).1
  let d := ready r₁ M.bits [] (encode result).reverse sourceWidth targetWidth frame
  have h₂ := transfer_eval d 9 8 0 1 (by decide) (by decide)
  have he₂ : afterTransfer d 9 8 0 1 =
      ready (readRegs r₁ 0 1 none) M.bits (encode result) [] sourceWidth targetWidth frame :=
    transfer_packed_state r₁ (encode result) M.bits sourceWidth targetWidth frame
  have hl : (d.stacks 9).length = 4*baseWidth p μ := by
    simp [d,ready,state,stackArray,Fin.addCases,Fin.coe_ofNat_eq_mod]
  refine ⟨n+(3*(4*baseWidth p μ)+3),?_,readRegs r₁ 0 1 none,?_⟩
  · simp only [quadWords,List.length_cons,List.length_nil] at hn
    omega
  · rw [hl, he₂] at h₂
    exact Eval.seq h₁ (by simpa only [d, result, encode] using h₂)

abbrev program : Program 8 20 (StructuredCalls.size coefficientLift+1) :=
  StructuredCalls.compiled coefficientLift 8 8

theorem program_runs (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (a : Quad (Word (baseWidth p 1))) (sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ regs', RunsIn program (2100 * (baseWidth p 1 + baseWidth p μ + 2)^2)
      ((ready regs M.bits (encode a) [] sourceWidth targetWidth frame).withPC (some program.entry))
      ((ready regs' M.bits (encode (SubexpWordLift.liftQuadRun p μ M a).1) []
        sourceWidth targetWidth frame).withPC none) := by
  obtain ⟨n,hn,rf,hr⟩ := coefficientLift_eval p μ M hμ regs a sourceWidth targetWidth frame hb hB
  refine ⟨rf,n+1,?_,StructuredCalls.compiled_halt_trace hr 8 8⟩
  have hcost := SubexpWordLiftMachine.runtimeBound_uniform
    (baseWidth p 1) (baseWidth p μ) M.bits.length M.length_le
  have hsq : baseWidth p 1 + baseWidth p μ + 2 ≤ (baseWidth p 1 + baseWidth p μ + 2)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left (baseWidth p 1 + baseWidth p μ + 2)
        (show 1 ≤ baseWidth p 1 + baseWidth p μ + 2 by omega)
  unfold wordCost at hn
  omega

theorem program_primitive (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (a : Quad (Word (baseWidth p 1))) (sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ regs', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (2100 * (baseWidth p 1 + baseWidth p μ + 2)^2))
      (primitiveCfg program
        ((ready regs M.bits (encode a) [] sourceWidth targetWidth frame).withPC (some program.entry)))
      (primitiveCfg program
        ((ready regs' M.bits (encode (SubexpWordLift.liftQuadRun p μ M a).1) []
          sourceWidth targetWidth frame).withPC none)) := by
  obtain ⟨rf,hr⟩ := program_runs p μ M hμ regs a sourceWidth targetWidth frame hb hB
  exact ⟨rf,primitive_execution _ hr⟩

end SubexponentialSAT.SubexpFlatLift

end OAI.Algorithms
