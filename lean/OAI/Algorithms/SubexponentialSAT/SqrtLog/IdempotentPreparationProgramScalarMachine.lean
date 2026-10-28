import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramBounds
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

abbrev Reg := Fin 12

def port : Reg → Fin 41 := ![17,18,19,20,21,23,24,25,27,28,30,31]

theorem port_injective : Function.Injective port := by decide
@[simp] theorem port_ge (i : Reg) : 8 ≤ (port i).val := by fin_cases i <;> decide
@[simp] theorem port_ne38 (i : Reg) : port i ≠ 38 := by fin_cases i <;> decide
@[simp] theorem port_ne40 (i : Reg) : port i ≠ 40 := by fin_cases i <;> decide

inductive Op where
  | add (out left right : Reg)
  | mul (out left right : Reg)

def Op.command : Op → Cmd 8 41
  | .add o l r => binary wordAddProgram (port o) (port l) (port r)
  | .mul o l r => binary wordMulProgram (port o) (port l) (port r)

variable (p t : ℕ) [Fact p.Prime]
abbrev Values := Reg → Word (baseWidth p t)

def Op.eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) : Op → Values p t
  | .add o l r => Function.update v o (SubexpPreparedQuartic.wordAdd p t M (v l) (v r)).1
  | .mul o l r => Function.update v o (SubexpPreparedQuartic.wordMul p t M (v l) (v r)).1

def Encoded (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) (d : Data) : Prop :=
  Rest d M.bits ∧ ∀ i, d.stacks (port i)=(v i).val

def Frame (d e : Data) : Prop := ∀ j, (∀ i, port i≠j) → e.stacks j=d.stacks j

omit [Fact (Nat.Prime p)] in
theorem encoded_update (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d e : Data) (o : Reg) (w : Word (baseWidth p t)) (h : Encoded p t M v d)
    (he : e.stacks=Function.update d.stacks (port o) w.val) :
    Encoded p t M (Function.update v o w) e ∧ Frame d e := by
  constructor
  · constructor
    · constructor
      · intro i
        have hi : low i≠port o := by
          intro hh
          have hv := congrArg Fin.val hh
          have hg:=port_ge o
          dsimp [low] at hv
          omega
        simpa [he,hi] using h.1.1 i
      · simpa [he,Ne.symm (port_ne38 o)] using h.1.2
    · intro i
      by_cases hi : i=o
      · subst i; simp [he]
      · have hp : port i≠port o := fun hh => hi (port_injective hh)
        simpa [he,hi,hp] using h.2 i
  · intro j hj
    simp [he,Ne.symm (hj o)]

def stepBudget : ℕ := 6000*(baseWidth p t+1)^2+25*baseWidth p t+21

theorem Op.command_eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d : Data) (op : Op) (h : Encoded p t M v d) :
    ∃ n e, Eval op.command n d e ∧ Encoded p t M (op.eval p t M v) e ∧
      Frame d e ∧ n ≤ stepBudget p t := by
  cases op with
  | add o l r =>
      obtain ⟨n,e,he,hes,hn⟩:=add_eval p t M d (port o) (port l) (port r)
        (v l) (v r) h.1 (port_ge o) (port_ge l) (port_ge r)
        (port_ne38 o) (port_ne38 l) (port_ne38 r) (h.2 l) (h.2 r)
      have hx:=encoded_update p t M v d e o _ h hes
      refine ⟨n,e,he,hx.1,hx.2,?_⟩
      rw [h.2 o,(v o).property] at hn
      dsimp [stepBudget]
      omega
  | mul o l r =>
      obtain ⟨n,e,he,hes,hn⟩:=mul_eval p t M d (port o) (port l) (port r)
        (v l) (v r) h.1 (port_ge o) (port_ge l) (port_ge r)
        (port_ne38 o) (port_ne38 l) (port_ne38 r) (h.2 l) (h.2 r)
      have hx:=encoded_update p t M v d e o _ h hes
      refine ⟨n,e,he,hx.1,hx.2,?_⟩
      rw [h.2 o,(v o).property] at hn
      dsimp [stepBudget]
      omega

def sequence : List Op → Cmd 8 41
  | [] => .base .skip
  | a::as => .seq a.command (sequence as)

def run (M : SubexpPreparedQuartic.Modulus p t) : List Op → Values p t → Values p t
  | [], v => v
  | a::as, v => run M as (a.eval p t M v)

theorem sequence_eval (M : SubexpPreparedQuartic.Modulus p t) (ops : List Op)
    (v : Values p t) (d : Data) (h : Encoded p t M v d) :
    ∃ n e, Eval (sequence ops) n d e ∧ Encoded p t M (run p t M ops v) e ∧
      Frame d e ∧ n ≤ ops.length * stepBudget p t := by
  induction ops generalizing v d with
  | nil => exact ⟨0,d,.base (.skip _),h,fun _ _=>rfl,by simp⟩
  | cons a as ih =>
      obtain ⟨na,da,ha,hva,hfa,hna⟩:=a.command_eval p t M v d h
      obtain ⟨nb,db,hb,hvb,hfb,hnb⟩:=ih _ da hva
      refine ⟨na+nb,db,ha.seq hb,hvb,?_,?_⟩
      · intro j hj; exact (hfb j hj).trans (hfa j hj)
      · simp only [List.length_cons]; nlinarith

/-- Cache registers: 0=zero,1=one,2=-2,3=3,4=-6,5=7,
6,7=temporary,8=half,9=-1,10=twice-half,11=-three-half. -/
def constants : List Op :=
  [.add 6 1 1, .add 3 6 1, .add 2 9 9, .mul 4 2 3,
   .add 5 3 3, .add 5 5 1, .add 8 1 0]

def halfStep : List Op := [.add 6 8 8, .add 7 6 8, .add 8 7 9]

def finalCoefficients : List Op := [.add 10 8 8, .add 6 10 8, .mul 11 6 9]

def loopPorts : UnaryForPrograms.Ports 8 41 := ⟨40,0,7⟩

abbrev halfLoop : Cmd 8 41 := UnaryForPrograms.forCmd loopPorts (sequence halfStep)

def iterate (M : SubexpPreparedQuartic.Modulus p t) : ℕ → Values p t → Values p t
  | 0,v => v
  | n+1,v => iterate M n (run p t M halfStep v)

def iterateForward (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) : ℕ → Values p t
  | 0 => v
  | n+1 => run p t M halfStep (iterateForward M v n)

theorem halfLoop_eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d : Data) (h : Encoded p t M v d) :
    ∃ n e, Eval halfLoop n d e ∧
      Encoded p t M (iterateForward p t M v (d.stacks 40).length) e ∧
      e.stacks 40=[] ∧
      (∀ j, j≠40 → (∀ i, port i≠j) → e.stacks j=d.stacks j) ∧
      n ≤ (d.stacks 40).length*(3*stepBudget p t+2)+2 := by
  let I (i : ℕ) (e : Data) : Prop :=
    Encoded p t M (iterateForward p t M v i) e ∧
    ∀ j, j≠40 → (∀ a, port a≠j) → e.stacks j=d.stacks j
  have stable : UnaryForPrograms.FrameStable loopPorts I := by
    intro i a b hab ha
    constructor
    · constructor
      · constructor
        · intro j
          rw [←hab (low j) (by intro hh; have hv:=congrArg Fin.val hh; dsimp [low,loopPorts] at hv; omega)]
          exact ha.1.1.1 j
        · rw [←hab 38 (by decide)]; exact ha.1.1.2
      · intro j
        rw [←hab (port j) (port_ne40 j)]
        exact ha.1.2 j
    · intro j hj hjs; rw [←hab j hj]; exact ha.2 j hj hjs
  have spec : UnaryForPrograms.BodySpec loopPorts (sequence halfStep) I
      (fun _=>3*stepBudget p t) := by
    intro i a ha
    obtain ⟨n,e,he,hv,hf,hn⟩:=sequence_eval p t M halfStep _ a ha.1
    refine ⟨n,e,?_,he,hf 40 port_ne40,?_,?_⟩
    · simpa [halfStep] using hn
    · exact hv
    · intro j hj hjs; exact (hf j hjs).trans (ha.2 j hj hjs)
  obtain ⟨n,e,he,hi,h40,hn⟩:=UnaryForPrograms.for_correct loopPorts (sequence halfStep) I
    (fun _=>3*stepBudget p t) stable spec d ⟨h,fun _ _ _=>rfl⟩
  refine ⟨n,e,he,hi.1,h40,hi.2,?_⟩
  have bs : ∀ n i, CounterForPrograms.budgetSum (fun _=>3*stepBudget p t) i n = n*(3*stepBudget p t) := by
    intro n; induction n with
    | zero => intro i; simp [CounterForPrograms.budgetSum]
    | succ n ih => intro i; simp [CounterForPrograms.budgetSum,ih]; ring
  simp only [loopPorts,bs] at hn
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
