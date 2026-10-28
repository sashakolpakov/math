import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBase

namespace OAI.Algorithms

/-! The actual native multiplication call in the wide factor loop. This
adapter derives its execution from the concrete sparse product program and
retains an exact frame, including every outer factor/source tape. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

def lowReady (a : Data) (e : MomentsProgram.Product.Store) : Prop :=
  ∀ i : Fin 56, a.stacks (nativeStacks (Memory.lowPort i)) =
    MomentsProgram.Product.tapes e i

def nativeHigh (a : Data) (i : Fin 40) : List Bool :=
  a.stacks (nativeStacks (Memory.highPort i))

theorem project_native (a : Data) (e : MomentsProgram.Product.Store) (h : lowReady a e) :
    projectState nativeRegisters nativeStacks a =
      Memory.state (a.regs ∘ nativeRegisters) (MomentsProgram.Product.tapes e) (nativeHigh a) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    induction i using Fin.addCases (m := 56) (n := 40) with
    | left i =>
        change a.stacks (nativeStacks (Memory.lowPort i)) =
          Memory.tapes _ _ (Memory.lowPort i)
        rw [Memory.tapes_low]
        exact h i
    | right i =>
        change a.stacks (nativeStacks (Memory.highPort i)) =
          Memory.tapes _ _ (Memory.highPort i)
        rw [Memory.tapes_high]
        rfl

private theorem product_embed_stacks (a : Data) (e : MomentsProgram.Product.Store)
    (h : lowReady a e) (rr : Fin 8 → Bool) (word : List Bool) :
    (embedState nativeRegisters nativeStacks a
      (Memory.state rr (MomentsProgram.Product.tapes e)
        (ProductCallback.resultHigh (nativeHigh a) word))).stacks =
      Function.update (Function.update a.stacks 61 []) 67 word := by
  funext i
  by_cases hin : ∃ j, nativeStacks j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [embedState_stack nativeRegisters nativeStacks a _ nativeStacks_injective j]
    induction j using Fin.addCases (m := 56) (n := 40) with
    | left j =>
      have h61 : nativeStacks (Memory.lowPort j) ≠ 61 := by
        intro he; have hv := congrArg Fin.val he
        change j.val = 61 at hv
        omega
      have h67 : nativeStacks (Memory.lowPort j) ≠ 67 := by
        intro he; have hv := congrArg Fin.val he
        change j.val = 67 at hv
        omega
      change Memory.tapes _ _ (Memory.lowPort j) =
        Function.update (Function.update a.stacks 61 []) 67 word
          (nativeStacks (Memory.lowPort j))
      rw [Memory.tapes_low,Function.update_of_ne h67,Function.update_of_ne h61]
      exact (h j).symm
    | right j =>
      change Memory.tapes _ _ (Memory.highPort j) =
        Function.update (Function.update a.stacks 61 []) 67 word
          (nativeStacks (Memory.highPort j))
      rw [Memory.tapes_high]
      fin_cases j <;>
        simp [ProductCallback.resultHigh,nativeHigh,nativeStacks,Memory.highPort]
  · have h61 : i ≠ 61 := by intro he; subst i; exact hin ⟨61,rfl⟩
    have h67 : i ≠ 67 := by intro he; subst i; exact hin ⟨67,rfl⟩
    rw [embedState_stack_frame nativeRegisters nativeStacks a _ i hin]
    simp [h61,h67]

theorem multiply_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (ha : a.stacks 67 = MomentsProgram.Product.bytes left)
    (hb : a.stacks 61 = MomentsProgram.Product.bytes right)
    (htmp : a.stacks 70 = []) :
    let result := MomentsProgram.Product.run p t M cache table u J left right []
    ∃ k b, k ≤ 9*(MomentsProgram.Product.bytes left).length+
        11*(MomentsProgram.Product.bytes right).length+9*(MomentsProgram.Product.bytes result).length+
        MomentsProgram.Product.work p t M cache table u J left right []+30 ∧
      Eval multiply k a b ∧
      b.stacks = Function.update (Function.update a.stacks 61 []) 67 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val
    (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)
  obtain ⟨k,hk,rr,he⟩ := ProductCallback.eval p t M cache hz table degree width hd hw u J left right
    (a.regs ∘ nativeRegisters) (nativeHigh a) ha hb htmp
  have hp := project_native a e hlo
  rw [← hp] at he
  have hc := eval_call_from_state
    (compiled (productAdapter product) 61 67) nativeRegisters nativeStacks a
    nativeRegisters_injective nativeStacks_injective (compiled_halt_trace he 61 67)
  exact ⟨k+1,_,by omega,hc,product_embed_stacks a e hlo rr _⟩

theorem lowReady_move (a : Data) (e : MomentsProgram.Product.Store)
    (h : lowReady a e) (src dst : Fin 768) (hs : 56 ≤ src.val) (hd : 56 ≤ dst.val) :
    lowReady (moved a src dst) e := by
  intro i
  have hsrc : nativeStacks (Memory.lowPort i) ≠ src := by
    intro he; have hv := congrArg Fin.val he
    change i.val = src.val at hv
    omega
  have hdst : nativeStacks (Memory.lowPort i) ≠ dst := by
    intro he; have hv := congrArg Fin.val he
    change i.val = dst.val at hv
    omega
  simpa only [moved,Function.update_of_ne hsrc,Function.update_of_ne hdst] using h i

/-- One factor is computed on67 and multiplied into the persistent running
product151. All three moves and the native product execution are charged. -/
theorem accumulate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151 = MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67 = MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61 = []) (h70 : a.stacks 70 = []) (h159 : a.stacks 159 = []) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 18*(MomentsProgram.Product.bytes seed).length+
        20*(MomentsProgram.Product.bytes factor).length+18*(MomentsProgram.Product.bytes result).length+
        MomentsProgram.Product.work p t M cache table u J seed factor []+54 ∧
      Eval accumulate k a b ∧
      b.stacks = Function.update (Function.update a.stacks 67 []) 151 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val
    (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)
  let a1 := moved a 67 61
  let a2 := moved a1 151 67
  have h1 := move_eval a 67 61 (by decide) (by decide) (by decide) h159
  have h2 := move_eval a1 151 67 (by decide) (by decide) (by decide)
    (by simpa [a1,moved] using h159)
  have hlo2 : lowReady a2 e := lowReady_move a1 e
    (lowReady_move a e hlo 67 61 (by decide) (by decide)) 151 67 (by decide) (by decide)
  obtain ⟨kp,bp,hkp,hp,hbp⟩ := multiply_eval p t M cache hz table degree width hd hw u J seed factor a2 hlo2
    (by simpa [a2,a1,moved] using hseed)
    (by simpa [a2,a1,moved,h61] using hfactor)
    (by simpa [a2,a1,moved] using h70)
  have hp159 : bp.stacks 159 = [] := by simpa [hbp,a2,a1,moved] using h159
  have h3 := move_eval bp 67 151 (by decide) (by decide) (by decide) hp159
  let result := MomentsProgram.Product.run p t M cache table u J seed factor []
  have hp67 : bp.stacks 67 = MomentsProgram.Product.bytes result := by simp [hbp,result]
  have hf : (moved bp 67 151).stacks =
      Function.update (Function.update a.stacks 67 []) 151 (MomentsProgram.Product.bytes result) := by
    funext i
    by_cases hi67 : i = 67
    · subst i; simp [moved,hbp,a2,a1]
    by_cases hi151 : i = 151
    · subst i; simp [moved,hbp,a2,a1,result]
    by_cases hi61 : i = 61
    · subst i; simp [moved,hbp,a2,a1,h61]
    · simp [moved,hbp,a2,a1,hi67,hi151,hi61]
  refine ⟨9*(a.stacks 67).length+8+(9*(a1.stacks 151).length+8+
    (kp+(9*(bp.stacks 67).length+8))),moved bp 67 151,?_,h1.seq (h2.seq (hp.seq h3)),hf⟩
  have hlen : a1.stacks 151 = MomentsProgram.Product.bytes seed := by
    simpa [a1,moved] using hseed
  rw [hfactor,hlen,hp67]
  dsimp only [result]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
