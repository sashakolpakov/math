import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorArithmetic

namespace OAI.Algorithms

/-! Paid cleanup and multiplication after a real factor service. The running
product remains on151 and all source/cache tapes are framed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

abbrev cleared := LeafAssignmentSetupProgram.cleared

theorem clear_eval (a : Data) (i : Fin 768) :
    Eval (clear i) (2*(a.stacks i).length+3) a (cleared a i) :=
  LeafAssignmentSetupProgram.clear_eval a i

theorem lowReady_clear (a : Data) (e : MomentsProgram.Product.Store)
    (h : lowReady a e) (j : Fin 768) (hj : 56 ≤ j.val) :
    lowReady (cleared a j) e := by
  intro i
  have hn : nativeStacks (Memory.lowPort i) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val=j.val at hv
    omega
  simpa only [cleared,LeafAssignmentSetupProgram.cleared,Function.update_of_ne hn] using h i

def productBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d)) : ℕ :=
  let result := MomentsProgram.Product.run p t M cache table u J seed factor []
  18*(MomentsProgram.Product.bytes seed).length+
    20*(MomentsProgram.Product.bytes factor).length+18*(MomentsProgram.Product.bytes result).length+
    MomentsProgram.Product.work p t M cache table u J seed factor []+54

/-- The actual suffix shared by the marked and ordinary hash branches. -/
theorem marked_tail_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 2*(a.stacks 62).length+3+productBudget p t M cache table u J seed factor ∧
      Eval (.seq (clear 62) accumulate) k a b ∧
      b.stacks=Function.update (Function.update (Function.update a.stacks 62 []) 67 [])
        151 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let c := cleared a 62
  obtain ⟨k,b,hk,he,hb⟩ := accumulate_eval p t M cache hz table degree width hd hw u J seed factor c
    (lowReady_clear a _ hlo 62 (by decide))
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hseed)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hfactor)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h61)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h70)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h159)
  exact ⟨_,b,Nat.add_le_add_left hk _,(clear_eval a 62).seq he,hb⟩

theorem hash_tail_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 2*(a.stacks 68).length+2*(a.stacks 62).length+6+
        productBudget p t M cache table u J seed factor ∧
      Eval (.seq (clear 68) (.seq (clear 62) accumulate)) k a b ∧
      b.stacks=Function.update (Function.update (Function.update
        (Function.update a.stacks 68 []) 62 []) 67 []) 151 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let c := cleared a 68
  obtain ⟨k,b,hk,he,hb⟩ := marked_tail_eval p t M cache hz table degree width hd hw u J seed factor c
    (lowReady_clear a _ hlo 68 (by decide))
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hseed)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hfactor)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h61)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h70)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h159)
  have hc : c.stacks 62=a.stacks 62 := by simp [c,LeafAssignmentSetupProgram.cleared]
  rw [hc] at hk
  exact ⟨_,b,by omega,(clear_eval a 68).seq he,hb⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
