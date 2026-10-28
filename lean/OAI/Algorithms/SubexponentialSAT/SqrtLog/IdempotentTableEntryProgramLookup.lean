import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramSubtract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev Data := State 8 4

/-- The code alphabet is 0,1,3,-2,-6,7 in that order. -/
def codeValue (c : Fin 6) : ℤ := ![0,1,3,-2,-6,7] c
def codeBits (c : Fin 6) : Fin 3 → Bool :=
  ![decide (c.val % 2 = 1), decide (c.val / 2 % 2 = 1), decide (c.val / 4 = 1)]

def outputPort (b : Fin 3) : Fin 8 := ⟨5+b.val,by omega⟩

def setOutput (r : Fin 8 → Bool) (c : Fin 6) : Fin 8 → Bool :=
  ![r 0,r 1,r 2,r 3,r 4,codeBits c 0,codeBits c 1,codeBits c 2]

abbrev emit (c : Fin 6) : Cmd 8 4 := .base
  (SubexpParameterProgram.atoms
    [.set 5 (codeBits c 0), .set 6 (codeBits c 1), .set 7 (codeBits c 2)])

theorem emit_eval (d : Data) (c : Fin 6) :
    Eval (emit c) 3 d ⟨setOutput d.regs c,d.stacks⟩ := by
  convert Eval.base (SubexpParameterProgram.atoms_eval
    [.set 5 (codeBits c 0), .set 6 (codeBits c 1), .set 7 (codeBits c 2)] d) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [setOutput,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  · rfl

def lookup : List (Fin 6) → Cmd 8 4
  | [] => emit 0
  | c :: cs => .seq (.base (.atom (.pop 2 0 1))) (.ite 1 (lookup cs) (emit c))

def data (r : Fin 8 → Bool) (xs ys zs bs : List Bool) : Data :=
  ⟨r,![xs,ys,zs,bs]⟩

theorem popLookup (r : Fin 8 → Bool) (xs ys zs bs : List Bool) :
    Eval (.base (.atom (.pop 2 0 1))) 1 (data r xs ys zs bs)
      (data (readRegs r 0 1 zs.head?) xs ys zs.tail bs) := by
  convert Eval.base (StructuredProgram.Eval.atom (.pop 2 0 1)
    (data r xs ys zs bs)) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,execInstr]

theorem lookup_eval (cs : List (Fin 6)) (n : ℕ) (r : Fin 8 → Bool)
    (xs ys bs : List Bool) :
    ∃ steps rf zs, steps ≤ 2*cs.length+3 ∧
      Eval (lookup cs) steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ b : Fin 3, rf (outputPort b) = codeBits (cs[n]?.getD 0) b) ∧ zs.length ≤ n := by
  induction cs generalizing n r with
  | nil =>
      refine ⟨3,setOutput r 0,List.replicate n true,by simp,emit_eval _ 0,?_,by simp⟩
      intro b; fin_cases b <;> simp [setOutput,outputPort]
  | cons c cs ih =>
      cases n with
      | zero =>
          let rr := readRegs r (0 : Fin 8) 1 none
          have he := (popLookup r xs ys [] bs).seq
            (Eval.ite_false (test := 1) (yes := lookup cs) (by simp [data,readRegs])
              (emit_eval (data rr xs ys [] bs) c))
          refine ⟨5,setOutput rr c,[],by simp only [List.length_cons] ; omega,he,?_,by simp⟩
          intro b
          fin_cases b <;> simp [setOutput, outputPort]
      | succ n =>
          let rr := readRegs r (0 : Fin 8) 1 (some true)
          obtain ⟨steps,rf,zs,hcost,he,hbits,hz⟩ := ih n rr
          refine ⟨steps+2,rf,zs,by simp only [List.length_cons] ; omega,?_,?_,by omega⟩
          · simpa [lookup,List.replicate_succ,Nat.add_comm,Nat.add_left_comm,
              Nat.add_assoc] using
              (popLookup r xs ys (true :: List.replicate n true) bs).seq
                (Eval.ite_true (test := 1) (no := emit c) (by simp [data,readRegs]) he)
          · simpa using hbits

def coefficientsAt : ℕ → List (Fin 6)
  | 0 => [1,0,0,0,0]
  | 1 => [0,1,0,0,0]
  | 2 => [0,0,1,0,0]
  | 3 => [0,3,2,1,0]
  | _ => [0,4,5,2,1]

theorem coefficientsAt_length (a : ℕ) : (coefficientsAt a).length = 5 := by
  rcases a with _ | _ | _ | _ | a <;> rfl

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
