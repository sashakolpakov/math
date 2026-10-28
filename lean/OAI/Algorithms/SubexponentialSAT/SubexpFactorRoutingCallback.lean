import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingCalls

namespace OAI.Algorithms

/-! One actual factor-routing step consumes the aligned assignment word. -/

namespace SubexponentialSAT.SubexpFactorRoutingCallback

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorRoutingControl
open SubexpFactorRoutingCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def workPorts : List (Fin 48) := [10,11,14,15,16,17,18,19,20,21,22,24,25,26,27,28]
def WorkClean (d : Data) : Prop := ∀ i ∈ workPorts, d.stacks i = []

theorem callback_eval {r Q : ℕ} (w : MulticolorTypes.Word r Q)
    (t : Fin Q) (g : Fin r) (payload rest : List Bool) (d : Data)
    (hc : WorkClean d)
    (h7 : d.stacks 7 = Subexp.ReadPlan.encodeWord w ++ rest)
    (h9 : d.stacks 9 = payload.reverse)
    (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r)
    (h12 : d.stacks 12 = unary g.val) (h13 : d.stacks 13 = unary t.val) :
    ∃ n ≤ callbackBudget (d.stacks 5).length t.val r g.val payload.length,
      ∃ regs : Fin 16 → Bool,
      (∀ i : Fin 16, 5 ≤ i.val → regs i = d.regs i) ∧
      Eval callback n d
        ⟨regs, Function.update (Function.update (Function.update d.stacks 7 rest) 9 []) 23
          (if w t = g then Subexp.TupleProgram.prependRecord payload (d.stacks 23)
           else d.stacks 23)⟩ := by
  have h10 := hc 10 (by simp [workPorts])
  have h11 := hc 11 (by simp [workPorts])
  have h20 := hc 20 (by simp [workPorts])
  have h21 := hc 21 (by simp [workPorts])
  have h22 := hc 22 (by simp [workPorts])
  have h26 := hc 26 (by simp [workPorts])
  have hword : (Subexp.ReadPlan.encodeWord w).length = (d.stacks 5).length := by
    simpa only [Subexp.ReadPlan.encodeWord_length, Subexp.ReadPlan.wordWidth] using h5.symm
  let a := pulled d (Subexp.ReadPlan.encodeWord w) rest
  have he1 := pullWord_eval d (Subexp.ReadPlan.encodeWord w) rest h7 hword.symm h10 h20 h21 h26
  have hac : ∀ i ∈ ([11,14,15,16,17,18,19] : List (Fin 48)), a.stacks i = [] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [a, pulled] using hc _ (by simp [workPorts])
  obtain ⟨nr, hnr, he2⟩ := readColor_eval w t a
    (by simp [a, pulled]) (by simpa [a, pulled] using h13)
    (by simpa [a, pulled] using h4) hac
  let b := colored a (w t).val
  let c := cleared b 10
  let e := afterCopy c 12 22 0 1
  have he3 := clear_eval b 10
  have he4 := copy_eval c 12 22 (by decide) (by decide) (by decide)
    (by simpa [c, cleared, b, colored, a, pulled] using h26)
  have he11 : e.stacks 11 = unary (w t).val := by
    simp [e, afterCopy, StackRoutines.copyStacks, c, cleared, b, colored]
  have he22 : e.stacks 22 = unary g.val := by
    simp [e, afterCopy, StackRoutines.copyStacks, c, cleared, b, colored, a, pulled, h22, h12]
  obtain ⟨nc, hnc, rr, left, right, hflag, hrr, hleft, hright, he5⟩ := compareColors_eval e
  let f : Data := ⟨rr, Function.update (Function.update e.stacks 11 left) 22 right⟩
  let k := cleared f 11
  let z := cleared k 22
  have he6 := clear_eval f 11
  have he7 := clear_eval k 22
  have hz : z.stacks = Function.update d.stacks 7 rest := by
    funext i
    by_cases hi7 : i = 7 <;> by_cases hi10 : i = 10 <;>
      by_cases hi11 : i = 11 <;> by_cases hi22 : i = 22 <;>
      simp [z, k, f, cleared, e, afterCopy, StackRoutines.copyStacks, c, b, colored, a, pulled,
        hi7, hi10, hi11, hi22, h10, h11, h22]
  have hunary : (unary (w t).val = unary g.val) ↔ w t = g := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [List.length_replicate] using congrArg List.length h
    · intro h; rw [h]
  have hzflag : z.regs 4 = decide (w t = g) := by
    change (readRegs (readRegs rr 0 1 none) 0 1 none) 4 = _
    simpa only [readRegs, Function.update_of_ne (by decide : (4 : Fin 16) ≠ 1),
      Function.update_of_ne (by decide : (4 : Fin 16) ≠ 0), he11, he22, hunary] using hflag
  have hzregs : ∀ i : Fin 16, 5 ≤ i.val → z.regs i = d.regs i := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have hrri := hrr i hi
    simpa [z, k, f, cleared, e, afterCopy, c, b, colored, a, pulled, readRegs, h0, h1] using hrri
  obtain ⟨ns, hns, last, he8, hlast, hlastregs⟩ := select_eval z (decide (w t = g)) hzflag
  have hlast' : last.stacks =
      Function.update (Function.update (Function.update d.stacks 7 rest) 9 []) 23
        (if w t = g then Subexp.TupleProgram.prependRecord payload (d.stacks 23)
         else d.stacks 23) := by
    rw [hlast, hz]
    simp [h9]
  have hfinal : last =
      ⟨last.regs, Function.update (Function.update (Function.update d.stacks 7 rest) 9 []) 23
        (if w t = g then Subexp.TupleProgram.prependRecord payload (d.stacks 23)
         else d.stacks 23)⟩ := state_ext rfl hlast'
  have he := he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq (he7.seq he8))))))
  change Eval callback _ d last at he
  rw [hfinal] at he
  refine ⟨_, ?_, last.regs, ?_, he⟩
  · have hb10 : (b.stacks 10).length = (d.stacks 5).length := by
      simpa [b, colored, a, pulled] using hword
    have hc12 : (c.stacks 12).length = g.val := by
      simp [c, cleared, b, colored, a, pulled, h12]
    have hf11 : (f.stacks 11).length = left.length := by simp [f]
    have hk22 : (k.stacks 22).length = right.length := by simp [k, cleared, f]
    have hz9 : (z.stacks 9).length = payload.length := by simp [hz, h9]
    rw [he11, List.length_replicate] at hnc hleft
    rw [he22, List.length_replicate] at hright
    rw [hz9] at hns
    simp only [hword, hb10, hc12, hf11, hk22]
    have hg := (w t).isLt
    unfold callbackBudget
    omega
  · intro i hi
    exact (hlastregs i hi).trans (hzregs i hi)

end SubexponentialSAT.SubexpFactorRoutingCallback

end OAI.Algorithms
