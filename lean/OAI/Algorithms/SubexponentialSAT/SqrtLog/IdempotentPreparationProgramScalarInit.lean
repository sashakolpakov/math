import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarMachine

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic

variable (p t : ℕ) [Fact p.Prime]

def zeroValue (shape : List Bool) (hshape : shape.length=baseWidth p t) : Word (baseWidth p t) :=
  ⟨padTo shape [],by simp [padTo_length,hshape]⟩

def initializePool : List Reg → Cmd 8 41
  | []=>.base .skip
  | i::is=>.seq (literal (port i) []) (initializePool is)

omit [Fact (Nat.Prime p)] in
/-- Initialization also tolerates the old binary exponent in cache slot 31. -/
theorem initialize_eval (M : SubexpPreparedQuartic.Modulus p t) (shape : List Bool)
    (slots : List Reg) (d : Data) (W : ℕ) (h : Rest d M.bits)
    (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval (initializePool slots) n d e ∧ Rest e M.bits ∧ e.stacks 12=shape ∧
      (∀i,e.stacks (port i)=if i∈slots then padTo shape [] else d.stacks (port i)) ∧
      Frame d e ∧ n ≤ slots.length * (23 * shape.length + 2 * W + 25) := by
  induction slots generalizing d with
  | nil=>exact ⟨0,d,.base (.skip _),h,h12,by simp,fun _ _=>rfl,by simp⟩
  | cons i is ih=>
      obtain ⟨na,a,ha,has,hna⟩:=literal_eval d M.bits shape (port i) [] h h12
        (port_ge i) (port_ne38 i)
      have har:Rest a M.bits := by
        constructor
        · intro j
          have hj:low j≠port i := by
            intro hh; have hv:=congrArg Fin.val hh; have hi:=port_ge i
            dsimp [low] at hv; omega
          simpa [has,hj] using h.1 j
        · simpa [has,Ne.symm (port_ne38 i)] using h.2
      have hi12:port i≠12 := by fin_cases i <;> decide
      have ha12:a.stacks 12=shape := by simp [has,hi12.symm,h12]
      have haw:∀j,(a.stacks (port j)).length ≤ W := by
        intro j
        by_cases hj:j=i
        · subst j; simpa [has,padTo_length] using hW
        · have hp:port j≠port i := fun hh=>hj (port_injective hh)
          simpa [has,hp] using hslots j
      obtain ⟨nb,b,hb,hbr,hb12,hbs,hbf,hnb⟩:=ih a har ha12 haw
      refine ⟨na+nb,b,ha.seq hb,hbr,hb12,?_,?_,?_⟩
      · intro j
        rw [hbs]
        by_cases hj:j∈is
        · simp [hj]
        · by_cases hji:j=i
          · subst j; simp [hj,has]
          · have hp:port j≠port i := fun hh=>hji (port_injective hh)
            simp [hj,hji,has,hp]
      · intro j hj
        rw [hbf j hj,has]
        simp [Ne.symm (hj i)]
      · have hi:=hslots i
        simp only [List.length_nil,mul_zero,add_zero] at hna
        simp only [List.length_cons]
        nlinarith

abbrev initializeAll : Cmd 8 41 := initializePool (List.finRange 12)

omit [Fact (Nat.Prime p)] in
theorem initializeAll_eval (M : SubexpPreparedQuartic.Modulus p t) (shape : List Bool)
    (hshape:shape.length=baseWidth p t) (d : Data) (W : ℕ) (h : Rest d M.bits)
    (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval initializeAll n d e ∧
      Encoded p t M (fun _=>zeroValue p t shape hshape) e ∧ e.stacks 12=shape ∧
      Frame d e ∧ n ≤ 12 * (23 * shape.length + 2 * W + 25) := by
  obtain ⟨n,e,he,her,he12,hes,hf,hn⟩:=initialize_eval p t M shape (List.finRange 12) d W h h12 hW hslots
  refine ⟨n,e,he,⟨her,?_⟩,he12,hf,by simpa using hn⟩
  intro i
  simpa [zeroValue] using hes i

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
