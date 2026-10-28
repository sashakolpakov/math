import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpScalarMachine
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMarshal

namespace OAI.Algorithms

/-!
# Streaming addition of serialized quartic coefficients

There are four calls to the actual modular-word machine. Width is supplied as
stack data. No instruction table is generated from a coefficient or its width.
-/

namespace SubexponentialSAT.SubexpFlatAdd

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def «stacks» (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (m := 14) (n := 6) (motive := fun _ => List Bool)
    (![x,y,[],[],[],modulus,[],[],left,right,width,counter,tmp,packed] :
      Fin 14 → List Bool) frame i

def state (regs : Fin 8 → Bool)
    (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, «stacks» x y modulus left right width counter tmp packed frame⟩

abbrev ready (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  state regs [] [] modulus left right width [] [] packed frame

private theorem take_left_state (regs : Fin 8 → Bool)
    (x modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (ready regs modulus (x ++ left) right width packed frame) 8 0 0 1 x left =
      state (readRegs regs 0 1 none) x [] modulus left right width [] [] packed frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTake, ready, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod
        ]

private theorem take_right_state (regs : Fin 8 → Bool)
    (x y modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (state regs x [] modulus left (y ++ right) width [] [] packed frame)
        9 1 0 1 y right =
      state (readRegs regs 0 1 none) x y modulus left right width [] [] packed frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTake, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod
        ]

private theorem transfer_sum_state (regs : Fin 8 → Bool)
    (x modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (state regs x [] modulus left right width [] [] packed frame) 0 13 0 1 =
      ready (readRegs regs 0 1 none) modulus left right width (x.reverse ++ packed) frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTransfer, ready, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.transferStacks ]

private theorem transfer_packed_state (regs : Fin 8 → Bool)
    (modulus width output : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (ready regs modulus [] [] width output.reverse frame) 13 8 0 1 =
      ready (readRegs regs 0 1 none) modulus output [] width [] frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTransfer, ready, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.transferStacks ]

def scalarPorts : Fin 8 → Fin 20 := Fin.castAdd 12

theorem scalarPorts_injective : Function.Injective scalarPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 20 => x.val) h

abbrev addScalar : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram ModularRingPrograms.wordAddProgram id scalarPorts)

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem addScalar_eval (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ))
    (left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    ∃ n ≤ 6000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval addScalar n
        (state regs x.val y.val M.bits left right width [] [] packed frame)
        (state regs' (SubexpPreparedQuartic.wordAdd p μ M x y).1.val []
          M.bits left right width [] [] packed frame) := by
  obtain ⟨regs', n, hn, ht⟩ := SubexpScalarMachine.wordAdd_run p μ M regs x y
  let a : State 8 8 := ⟨regs, ModularRingPrograms.extendSeven
    (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩
  let b : State 8 8 := ⟨regs', ModularRingPrograms.extendSeven
    (ModularDivisionPrograms.resting (SubexpPreparedQuartic.wordAdd p μ M x y).1.val
      M.bits []) []⟩
  let d := state regs x.val y.val M.bits left right width [] [] packed frame
  have ha : embedState id scalarPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intros; rfl
  have hb : embedState id scalarPorts d b =
      state regs' (SubexpPreparedQuartic.wordAdd p μ M x y).1.val []
        M.bits left right width [] [] packed frame := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
  have hr := eval_call_lifted ModularRingPrograms.wordAddProgram id scalarPorts d
    Function.injective_id scalarPorts_injective (a := a) (b := b) ht
  exact ⟨n, hn, regs', by simpa only [ha,hb,addScalar] using hr⟩

/-- One word from each flattened coefficient, followed by a real scalar add. -/
abbrev addOne : Cmd 8 20 :=
  .seq (takeWord 10 11 12 8 0 0 1)
    (.seq (takeWord 10 11 12 9 1 0 1)
      (.seq addScalar (.call (StackRoutines.transferProgram 0 13 (0 : Fin 8) 1))))

def wordCost (B : ℕ) : ℕ := 6000 * (B+1)^2 + 31*B + 25

theorem addOne_eval (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ))
    (left right width packed : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ wordCost (baseWidth p μ), ∃ regs',
      Eval addOne n
        (ready regs M.bits (x.val ++ left) (y.val ++ right) width packed frame)
        (ready regs' M.bits left right width
          ((SubexpPreparedQuartic.wordAdd p μ M x y).1.val.reverse ++ packed) frame) := by
  let regs₁ := readRegs regs 0 1 none
  let d₀ := ready regs M.bits (x.val ++ left) (y.val ++ right) width packed frame
  let d₁ := state regs₁ x.val [] M.bits left (y.val ++ right) width [] [] packed frame
  have h₁ : Eval (takeWord 10 11 12 8 0 0 1) (14*baseWidth p μ+11) d₀ d₁ := by
    have h := takeWord_eval d₀ 10 11 12 8 0 0 1 (by decide) (by decide)
      x.val left rfl rfl rfl (hwidth.trans x.property.symm)
    have he : afterTake d₀ 8 0 0 1 x.val left = d₁ :=
      take_left_state regs x.val M.bits left (y.val ++ right) width packed frame
    simpa only [x.property,he] using h
  let d₂ := state regs₁ x.val y.val M.bits left right width [] [] packed frame
  have h₂ : Eval (takeWord 10 11 12 9 1 0 1) (14*baseWidth p μ+11) d₁ d₂ := by
    have h := takeWord_eval d₁ 10 11 12 9 1 0 1 (by decide) (by decide)
      y.val right rfl rfl rfl (hwidth.trans y.property.symm)
    have he : afterTake d₁ 9 1 0 1 y.val right = d₂ := by
      simpa only [d₁,d₂,regs₁,StackRoutines.readRegs_reset] using
        take_right_state regs₁ x.val y.val M.bits left right width packed frame
    simpa only [y.property,he] using h
  obtain ⟨n, hn, regs₂, h₃⟩ := addScalar_eval p μ M regs₁ x y left right width packed frame
  let z := (SubexpPreparedQuartic.wordAdd p μ M x y).1
  let d₃ := state regs₂ z.val [] M.bits left right width [] [] packed frame
  have h₄ : Eval (.call (StackRoutines.transferProgram 0 13 (0 : Fin 8) 1))
      (3*baseWidth p μ+3) d₃
      (ready (readRegs regs₂ 0 1 none) M.bits left right width (z.val.reverse++packed) frame) := by
    have h := transfer_eval d₃ 0 13 0 1 (by decide) (by decide)
    have he : afterTransfer d₃ 0 13 0 1 =
        ready (readRegs regs₂ 0 1 none) M.bits left right width (z.val.reverse++packed) frame :=
      transfer_sum_state regs₂ z.val M.bits left right width packed frame
    have hl : (d₃.stacks 0).length = baseWidth p μ := z.property
    simpa only [hl,he] using h
  refine ⟨(14*baseWidth p μ+11)+(14*baseWidth p μ+11+(n+(3*baseWidth p μ+3))),
    ?_, readRegs regs₂ 0 1 none, Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))⟩
  unfold wordCost
  omega

def repeatAdd : ℕ → Cmd 8 20
  | 0 => .base .skip
  | n+1 => .seq addOne (repeatAdd n)

def flatten {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

def addWords : List (Word (baseWidth p μ)) → List (Word (baseWidth p μ)) →
    List (Word (baseWidth p μ))
  | x::xs, y::ys => (SubexpPreparedQuartic.wordAdd p μ M x y).1 :: addWords xs ys
  | _, _ => []

theorem repeatAdd_eval (regs : Fin 8 → Bool)
    (xs ys : List (Word (baseWidth p μ))) (hlen : xs.length = ys.length)
    (width packed : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ xs.length * wordCost (baseWidth p μ), ∃ regs',
      Eval (repeatAdd xs.length) n
        (ready regs M.bits (flatten xs) (flatten ys) width packed frame)
        (ready regs' M.bits [] [] width
          ((flatten (addWords p μ M xs ys)).reverse ++ packed) frame) := by
  induction xs generalizing ys regs packed with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      exact ⟨0,by simp,regs,by simpa [repeatAdd,flatten,addWords] using
        (Eval.base (StructuredProgram.Eval.skip (ready regs M.bits [] [] width packed frame)))⟩
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          obtain ⟨n,hn,r₁,h₁⟩ := addOne_eval p μ M regs x y (flatten xs) (flatten ys)
            width packed frame hwidth
          obtain ⟨m,hm,r₂,h₂⟩ := ih (regs := r₁) (ys := ys)
            (packed := (SubexpPreparedQuartic.wordAdd p μ M x y).1.val.reverse++packed) hlen'
          refine ⟨n+m,?_,r₂,?_⟩
          · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
            omega
          · simpa [repeatAdd,flatten,addWords,List.reverse_append,List.append_assoc] using Eval.seq h₁ h₂

abbrev coefficientAdd : Cmd 8 20 :=
  .seq (repeatAdd 4) (.call (StackRoutines.transferProgram 13 8 (0 : Fin 8) 1))

def quadWords {B : ℕ} (a : Quad (Word B)) : List (Word B) := [a.c0,a.c1,a.c2,a.c3]
abbrev encode {B : ℕ} (a : Quad (Word B)) : List Bool := flatten (quadWords a)

@[simp] theorem encode_length {B : ℕ} (a : Quad (Word B)) : (encode a).length = 4*B := by
  simp [encode,quadWords,flatten,a.c0.property,a.c1.property,a.c2.property,a.c3.property]
  omega

omit [Fact (Nat.Prime p)] in
/-- The physical scalar marshaler produces the exact flat constant code,
including when the scalar input is not a canonical residue. -/
theorem marshalBits_eq_encode_constant (output shape : List Bool)
    (houtput : output.length = baseWidth p μ) (hshape : shape.length = baseWidth p μ) :
    SubexpQuarticMarshal.marshalBits output shape =
      encode (⟨⟨output,houtput⟩, SubexpPreparedQuartic.zeroWord p μ,
        SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ⟩ :
          Quad (Word (baseWidth p μ))) := by
  have ht : 3 * baseWidth p μ = baseWidth p μ + (baseWidth p μ + baseWidth p μ) := by omega
  change output ++ List.replicate (3 * shape.length) false =
    output ++ (List.replicate (baseWidth p μ) false ++
      (List.replicate (baseWidth p μ) false ++
        (List.replicate (baseWidth p μ) false ++ [])))
  rw [hshape, ht, List.replicate_add, List.replicate_add]
  simp only [List.append_nil]

omit [Fact (Nat.Prime p)] in
theorem encoded_constant_quotient (c : Fin 4 → ZMod (p^μ))
    (output : List Bool) (houtput : output.length = baseWidth p μ) :
    quotientDenote c
      ((⟨⟨output,houtput⟩, SubexpPreparedQuartic.zeroWord p μ,
        SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ⟩ :
          Quad (Word (baseWidth p μ))).map (wordValue p μ)) =
      LiftRing.of (QuarticSearch.poly c) (wordValue p μ ⟨output,houtput⟩) := by
  simp only [Quad.map, SubexpPreparedQuartic.zeroWord_value, quotientDenote_const]

theorem coefficientAdd_eval (regs : Fin 8 → Bool)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 4*wordCost (baseWidth p μ)+12*baseWidth p μ+3, ∃ regs',
      Eval coefficientAdd n
        (ready regs M.bits (encode a) (encode b) width [] frame)
        (ready regs' M.bits (encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) []
          width [] frame) := by
  have he : addWords p μ M (quadWords a) (quadWords b) =
      quadWords (SubexpPreparedQuartic.binaryAdd p μ M a b).1 := rfl
  obtain ⟨n,hn,r₁,h₁⟩ := repeatAdd_eval p μ M regs (quadWords a) (quadWords b) rfl
    width [] frame hwidth
  simp only [he,List.append_nil] at h₁
  let result := (SubexpPreparedQuartic.binaryAdd p μ M a b).1
  let d := ready r₁ M.bits [] [] width (encode result).reverse frame
  have h₂ := transfer_eval d 13 8 0 1 (by decide) (by decide)
  have he₂ : afterTransfer d 13 8 0 1 =
      ready (readRegs r₁ 0 1 none) M.bits (encode result) [] width [] frame :=
    transfer_packed_state r₁ M.bits width (encode result) frame
  have hl : (d.stacks 13).length = 4*baseWidth p μ := by
    simp [d,state,«stacks»,Fin.addCases,Fin.coe_ofNat_eq_mod]
  refine ⟨n+(3*(4*baseWidth p μ)+3),?_,readRegs r₁ 0 1 none,?_⟩
  · simp only [quadWords,List.length_cons,List.length_nil] at hn
    omega
  · exact Eval.seq h₁ (by simpa only [hl,he₂] using h₂)

abbrev program : Program 8 20 (StructuredCalls.size coefficientAdd+1) :=
  StructuredCalls.compiled coefficientAdd 8 8

theorem program_runs (regs : Fin 8 → Bool)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn program (4*wordCost (baseWidth p μ)+12*baseWidth p μ+4)
      ((ready regs M.bits (encode a) (encode b) width [] frame).withPC (some program.entry))
      ((ready regs' M.bits (encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) []
        width [] frame).withPC none) := by
  obtain ⟨n,hn,regs',hr⟩ := coefficientAdd_eval p μ M regs a b width frame hwidth
  exact ⟨regs',n+1,by omega,StructuredCalls.compiled_halt_trace hr 8 8⟩

theorem program_runs_uniform (regs : Fin 8 → Bool)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn program (25000 * (baseWidth p μ + 1)^2)
      ((ready regs M.bits (encode a) (encode b) width [] frame).withPC (some program.entry))
      ((ready regs' M.bits (encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) []
        width [] frame).withPC none) := by
  obtain ⟨regs', hr⟩ := program_runs p μ M regs a b width frame hwidth
  refine ⟨regs', hr.mono ?_⟩
  unfold wordCost
  have hsq : baseWidth p μ + 1 ≤ (baseWidth p μ + 1)^2 := by
    simpa only [Nat.mul_one, pow_two] using
      Nat.mul_le_mul_left (baseWidth p μ + 1)
        (Nat.succ_le_succ (Nat.zero_le (baseWidth p μ)))
  omega

/-- Primitive-machine refinement of addition of two flat four-word coefficients.
The finite program and its compilation overhead do not depend on p or mu. -/
theorem program_primitive (regs : Fin 8 → Bool)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (25000 * (baseWidth p μ + 1)^2))
      (primitiveCfg program
        ((ready regs M.bits (encode a) (encode b) width [] frame).withPC (some program.entry)))
      (primitiveCfg program
        ((ready regs' M.bits (encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) []
          width [] frame).withPC none)) := by
  obtain ⟨regs', hr⟩ := program_runs_uniform p μ M regs a b width frame hwidth
  exact ⟨regs', primitive_execution _ hr⟩

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
