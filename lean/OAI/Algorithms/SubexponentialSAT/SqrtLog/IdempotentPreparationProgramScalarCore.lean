import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramRegisters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing
open IdempotentProgram (storeResult storeResult_eval storedResult_stacks)

abbrev Data := State 8 41

def low : Fin 8 → Fin 41 := Fin.castAdd 33

theorem low_injective : Function.Injective low := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

/-- Arbitrary stacks outside the eight scalar-machine ports are framed. -/
abbrev callLow {l : ℕ} (p : Program 8 8 l) : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram p id low)

theorem callLow_eval {l : ℕ} (p : Program 8 8 l) (d : Data)
    (a b : State 8 8) (result : Fin 41 → List Bool) (n : ℕ)
    (hr : a.regs = d.regs)
    (ha : ∀ i, d.stacks (low i) = a.stacks i)
    (hb : ∀ i, result (low i) = b.stacks i)
    (hout : ∀ j, 8 ≤ j.val → result j = d.stacks j)
    (run : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    ∃ e, Eval (callLow p) n d e ∧ e.stacks = result := by
  have he := eval_call_lifted p id low d Function.injective_id low_injective run
  have hin : embedState id low d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro i; exact (congrFun hr i).symm
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · exact ha
    · intro i hi; rfl
  rw [hin] at he
  refine ⟨embedState id low d b, he, ?_⟩
  funext j
  by_cases hj : j.val < 8
  · let i : Fin 8 := ⟨j.val,hj⟩
    have hi : low i = j := Fin.ext rfl
    rw [←hi, embedState_stack _ _ _ _ low_injective]
    exact (hb i).symm
  · rw [embedState_stack_frame]
    · exact (hout j (by omega)).symm
    · rintro ⟨i,hi⟩
      have hval := congrArg Fin.val hi
      dsimp [low] at hval
      omega

def Rest (d : Data) (modulus : List Bool) : Prop :=
  (∀ i : Fin 8, d.stacks (low i) = if i = 5 then modulus else []) ∧ d.stacks 38 = []

def operands (d : Data) (left right : Fin 41) : Data :=
  ArithmeticCalls.afterCopy right 1 (ArithmeticCalls.afterCopy left 0 d)

abbrev prepare (left right : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt left 0 38) (ArithmeticCalls.copyAt right 1 38)

abbrev binary {l : ℕ} (p : Program 8 8 l) (target left right : Fin 41) : Cmd 8 41 :=
  .seq (prepare left right) (.seq (callLow p) (storeResult target))

theorem prepare_eval (d : Data) (left right : Fin 41) (m : List Bool)
    (h : Rest d m) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38) :
    Eval (prepare left right) (7*(d.stacks left).length+7*(d.stacks right).length+10)
      d (operands d left right) := by
  have hl0 : left ≠ 0 := by intro he; subst left; contradiction
  have hr0 : right ≠ 0 := by intro he; subst right; contradiction
  have hr1 : right ≠ 1 := by intro he; subst right; contradiction
  have h0 : d.stacks 0 = [] := by simpa [low] using h.1 0
  have h1 : d.stacks 1 = [] := by simpa [low] using h.1 1
  have a := ArithmeticCalls.copyAt_eval left 0 38 d hl0 hl38 (by decide) h0 h.2
  have b := ArithmeticCalls.copyAt_eval right 1 38 (ArithmeticCalls.afterCopy left 0 d)
    hr1 hr38 (by decide) (by simp [ArithmeticCalls.afterCopy,h1])
    (by simp [ArithmeticCalls.afterCopy,h.2])
  convert a.seq b using 1 <;>
    simp [operands,ArithmeticCalls.afterCopy,hr0] ; omega

theorem binary_eval {l : ℕ} (p : Program 8 8 l) (d : Data)
    (m x y out : List Bool) (target left right : Fin 41) (n : ℕ) (rf : Fin 8 → Bool)
    (h : Rest d m) (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left = x) (hy : d.stacks right = y)
    (run : Trace p n
      ⟨some p.entry, (operands d left right).regs, extendSeven (scalarInput x y m) []⟩
      ⟨none,rf,extendSeven (resting out m []) []⟩) :
    ∃ e, Eval (binary p target left right)
      (n+7*x.length+7*y.length+2*(d.stacks target).length+9*out.length+21) d e ∧
      e.stacks = Function.update d.stacks target out := by
  have hr0 : right ≠ 0 := by intro he; subst right; contradiction
  have ht0 : target ≠ 0 := by intro he; subst target; contradiction
  have prep := prepare_eval d left right m h hl hr hl38 hr38
  have hops : (operands d left right).stacks =
      Function.update (Function.update d.stacks 0 x) 1 y := by
    simp [operands,ArithmeticCalls.afterCopy,hr0,hx,hy]
  obtain ⟨e,he,hes⟩ := callLow_eval p (operands d left right)
    ⟨(operands d left right).regs,extendSeven (scalarInput x y m) []⟩
    ⟨rf,extendSeven (resting out m []) []⟩
    (Function.update d.stacks 0 out) n rfl (by
      intro i
      have hi := h.1 i
      fin_cases i <;> simp [hops,low,extendSeven,scalarInput,seven] at hi ⊢ <;> exact hi)
    (by
      intro i
      have hi := h.1 i
      fin_cases i <;> simp [low,extendSeven,resting,seven] at hi ⊢ <;> exact hi)
    (by
      intro j hj
      have hj0 : j ≠ 0 := by intro hh; subst j; contradiction
      have hj1 : j ≠ 1 := by intro hh; subst j; contradiction
      simp [hops,hj0,hj1]) run
  have store := storeResult_eval e target ht0 ht38 (by rw [hes]; simpa using h.2)
  refine ⟨IdempotentProgram.storedResult e target,?_,?_⟩
  · convert prep.seq (he.seq store) using 1 ;
      simp [hx,hy,hes,ht0] ; omega
  · rw [storedResult_stacks e target ht0,hes]
    have h0 : d.stacks 0 = [] := by simpa [low] using h.1 0
    funext j
    by_cases hjt : j=target
    · subst j; simp [ht0]
    · by_cases hj0 : j=0
      · subst j; simp [hjt,h0]
      · simp [hjt,hj0]

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)

theorem add_eval (d : Data) (target left right : Fin 41)
    (x y : Word (baseWidth p t)) (h : Rest d M.bits)
    (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left=x.val) (hy : d.stacks right=y.val) :
    ∃ n e, Eval (binary wordAddProgram target left right) n d e ∧
      e.stacks = Function.update d.stacks target (SubexpPreparedQuartic.wordAdd p t M x y).1.val ∧
      n ≤ 6000*(baseWidth p t+1)^2+23*baseWidth p t+2*(d.stacks target).length+21 := by
  obtain ⟨rf,n,hn,run⟩ := SubexpScalarMachine.wordAdd_run p t M (operands d left right).regs x y
  obtain ⟨e,he,hes⟩ := binary_eval wordAddProgram d M.bits x.val y.val _ target left right
    n rf h ht hl hr ht38 hl38 hr38 hx hy run
  refine ⟨_,e,he,hes,?_⟩
  rw [x.property,y.property,(SubexpPreparedQuartic.wordAdd p t M x y).1.property]
  omega

theorem mul_eval (d : Data) (target left right : Fin 41)
    (x y : Word (baseWidth p t)) (h : Rest d M.bits)
    (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left=x.val) (hy : d.stacks right=y.val) :
    ∃ n e, Eval (binary wordMulProgram target left right) n d e ∧
      e.stacks = Function.update d.stacks target (SubexpPreparedQuartic.wordMul p t M x y).1.val ∧
      n ≤ 6000*(baseWidth p t+1)^2+23*baseWidth p t+2*(d.stacks target).length+21 := by
  obtain ⟨rf,n,hn,run⟩ := SubexpScalarMachine.wordMul_run p t M (operands d left right).regs x y
  obtain ⟨e,he,hes⟩ := binary_eval wordMulProgram d M.bits x.val y.val _ target left right
    n rf h ht hl hr ht38 hl38 hr38 hx hy run
  refine ⟨_,e,he,hes,?_⟩
  rw [x.property,y.property,(SubexpPreparedQuartic.wordMul p t M x y).1.property]
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
