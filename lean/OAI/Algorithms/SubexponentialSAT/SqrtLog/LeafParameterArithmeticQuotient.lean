import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

structure QuotientPorts (S : ℕ) where
  left : Fin S
  right : Fin S
  out : Fin S
  work : Fin 6 ↪ Fin S
  out_ne_left : out ≠ left
  out_ne_right : out ≠ right
  work_ne_left : ∀ i, work i ≠ left
  work_ne_right : ∀ i, work i ≠ right
  work_ne_out : ∀ i, work i ≠ out

def QuotientReady {S : ℕ} (p : QuotientPorts S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

@[simp] theorem quotient_right_ne_work {S : ℕ} (p : QuotientPorts S) (i : Fin 6) :
    p.right ≠ p.work i := (p.work_ne_right i).symm

@[simp] theorem quotient_out_ne_work {S : ℕ} (p : QuotientPorts S) (i : Fin 6) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

@[simp] theorem quotient_right_ne_out {S : ℕ} (p : QuotientPorts S) :
    p.right ≠ p.out := p.out_ne_right.symm

def quotientStackMap {S : ℕ} (p : QuotientPorts S) : Fin 8 → Fin S :=
  ![p.work 0, p.work 1, p.work 2, p.work 3, p.work 4, p.right, p.work 5, p.out]

theorem quotientStackMap_injective {S : ℕ} (p : QuotientPorts S) :
    Function.Injective (quotientStackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quotientStackMap, p.work.injective.eq_iff, p.work_ne_right,
      p.work_ne_out, p.out_ne_right, Ne.symm p.out_ne_right]

abbrev quotientAt {S : ℕ} (p : QuotientPorts S) : Cmd 8 S :=
  .seq (ArithmeticCalls.copyAt p.left (p.work 5) (p.work 1))
    (.seq (.call (ProgramLinking.liftProgram ModularQuotientPrograms.quotientProgram
      id (quotientStackMap p))) (ArithmeticExpressionSupport.clearCmd (p.work 0)))

private theorem quotient_embed_start {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) :
    embedState id (quotientStackMap p) d
      ⟨(ArithmeticCalls.afterCopy p.left (p.work 5) d).regs,
        ModularQuotientPrograms.quotientStacks [] (d.stacks p.right) (d.stacks p.left) []⟩ =
      ArithmeticCalls.afterCopy p.left (p.work 5) d := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (quotientStackMap_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [ArithmeticCalls.afterCopy, quotientStackMap,
      ModularQuotientPrograms.quotientStacks, p.work.injective.eq_iff, hd.1, hd.2]
  · intro i hi
    have hn : i ≠ p.work 5 := fun h => hi ⟨6, h.symm⟩
    simp [ArithmeticCalls.afterCopy, hn]

private theorem quotient_embed_finish {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (rf : Fin 8 → Bool) (rem word : List Bool) :
    embedState id (quotientStackMap p) d
      ⟨rf, ModularQuotientPrograms.quotientStacks rem (d.stacks p.right) [] word⟩ =
      (⟨rf, Function.update (Function.update d.stacks p.out word) (p.work 0) rem⟩ : Data S) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (quotientStackMap_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [quotientStackMap, ModularQuotientPrograms.quotientStacks,
      p.work.injective.eq_iff, p.work_ne_out, hd.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨0, h.symm⟩
    have ho : i ≠ p.out := fun h => hi ⟨7, h.symm⟩
    simp [h0, ho]

/-- The only final stack change is the quotient output. All work and both
source words are preserved, including arbitrary leading-zero padding. -/
theorem quotientAt_eval {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (hp : 0 < BinaryArithmetic.toNat (d.stacks p.right)) :
    ∃ t rf word,
      Eval (quotientAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.left) / BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length = (d.stacks p.left).length ∧
      t ≤ 150 * ((d.stacks p.left).length + (d.stacks p.right).length + 1)^2 := by
  let a := ArithmeticCalls.afterCopy p.left (p.work 5) d
  have hc : Eval (ArithmeticCalls.copyAt p.left (p.work 5) (p.work 1))
      (7*(d.stacks p.left).length+5) d a :=
    ArithmeticCalls.copyAt_eval _ _ _ d (p.work_ne_left 5).symm
      (p.work_ne_left 1).symm (by simp [p.work.injective.eq_iff]) (hd.2 5) (hd.2 1)
  obtain ⟨rf,word,rem,⟨t,ht,he⟩,hl,hrl,hv,_⟩ :=
    ModularQuotientPrograms.quotient_value a.regs (d.stacks p.right) (d.stacks p.left) hp
  have hcall := eval_call_lifted ModularQuotientPrograms.quotientProgram id
    (quotientStackMap p) d Function.injective_id (quotientStackMap_injective p)
    (a := ⟨a.regs, ModularQuotientPrograms.quotientStacks []
      (d.stacks p.right) (d.stacks p.left) []⟩)
    (b := ⟨rf, ModularQuotientPrograms.quotientStacks rem (d.stacks p.right) [] word⟩) he
  rw [quotient_embed_start p d hd, quotient_embed_finish p d hd] at hcall
  let b : Data S :=
    ⟨rf, Function.update (Function.update d.stacks p.out word) (p.work 0) rem⟩
  have hb : Eval (ArithmeticExpressionSupport.clearCmd (p.work 0))
      (2*rem.length+3) b
      ⟨readRegs rf 0 1 none, Function.update d.stacks p.out word⟩ := by
    have hh := ArithmeticExpressionSupport.clear_eval (p.work 0) b
    have hs : Function.update b.stacks (p.work 0) [] =
        Function.update d.stacks p.out word := by
      funext i
      by_cases hi : i = p.work 0
      · subst i; simp [b, p.work_ne_out, hd.2]
      · simp [b, hi]
    simpa only [b, Function.update_self, hs] using hh
  refine ⟨7*(d.stacks p.left).length+5+(t+(2*rem.length+3)),
    readRegs rf 0 1 none, word, hc.seq (hcall.seq hb), hv, hl, ?_⟩
  rw [hrl]
  nlinarith

def quotientProgram {S : ℕ} (p : QuotientPorts S) := compiled (quotientAt p) p.left p.out

theorem quotientProgram_runs {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (hp : 0 < BinaryArithmetic.toNat (d.stacks p.right)) :
    ∃ rf word, RunsIn (quotientProgram p)
      (151*((d.stacks p.left).length+(d.stacks p.right).length+1)^2)
      (d.withPC (some (quotientProgram p).entry))
      ((⟨rf,Function.update d.stacks p.out word⟩ : Data S).withPC none) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.left) / BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length = (d.stacks p.left).length := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := quotientAt_eval p d hd hp
  have hpos : 0 < ((d.stacks p.left).length+(d.stacks p.right).length+1)^2 :=
    Nat.pow_pos (by omega)
  exact ⟨rf,word,⟨t+1,by nlinarith,compiled_halt_trace he p.left p.out⟩,hv,hl⟩

theorem quotientProgram_primitive {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (hp : 0 < BinaryArithmetic.toNat (d.stacks p.right)) :
    ∃ rf word, Computation.RunsIn (primitive (quotientProgram p)).step
      (primitiveOverhead (quotientProgram p) *
        (151*((d.stacks p.left).length+(d.stacks p.right).length+1)^2))
      (primitiveCfg (quotientProgram p) (d.withPC (some (quotientProgram p).entry)))
      (primitiveCfg (quotientProgram p)
        ((⟨rf,Function.update d.stacks p.out word⟩ : Data S).withPC none)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.left) / BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length = (d.stacks p.left).length := by
  obtain ⟨rf,word,hr,hv,hl⟩ := quotientProgram_runs p d hd hp
  exact ⟨rf,word,primitive_execution _ hr,hv,hl⟩

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
