import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramWeightScan
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! Fixed-code filtering of bounded-weight masks, copying a runtime unary
budget for each candidate. Rejected candidates are discarded immediately. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram.Filter

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 8 7

def ports : SubexponentialSAT.RecordPrograms.Ports 8 7 :=
  ⟨0,1,2,0,1,by decide,by decide,by decide,by decide⟩
def emitPorts : SubexponentialSAT.RecordPrograms.Ports 8 7 :=
  ⟨3,4,7,1,4,by decide,by decide,by decide,by decide⟩
def scanRegister : Fin 4 → Fin 8 := ![3,4,5,6]
def scanPort : Fin 2 → Fin 7 := ![2,6]
theorem scanRegister_injective : Function.Injective scanRegister := by decide
theorem scanPort_injective : Function.Injective scanPort := by decide

abbrev scan : Cmd 8 7 := .call (SubexponentialSAT.ProgramLinking.liftProgram WeightScan.program scanRegister scanPort)

theorem scan_eval (a : Data) :
    ∃ n ≤ 5 * (a.stacks 2).length + 4, ∃ b : Data,
      Eval scan n a b ∧ b.stacks 2 = [] ∧
      b.stacks 6 = (a.stacks 6).drop ((a.stacks 2).count true) ∧
      b.regs 6 = decide ((a.stacks 2).count true < (a.stacks 6).length) ∧
      (∀ i, i ≠ 2 → i ≠ 6 → b.stacks i = a.stacks i) ∧
      (∀ i, i.val < 3 → b.regs i = a.regs i) := by
  obtain ⟨n, hn, regs, ht, ha⟩ := WeightScan.program_trace
    (a.stacks 2) (a.stacks 6) (a.regs ∘ scanRegister)
  let small := WeightScan.state regs [] ((a.stacks 6).drop ((a.stacks 2).count true))
  have hstart : restrictState scanRegister scanPort a =
      WeightScan.state (a.regs ∘ scanRegister) (a.stacks 2) (a.stacks 6) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨m, hm, he⟩ := lifted_call WeightScan.program scanRegister scanPort
    scanRegister_injective scanPort_injective a small (5 * (a.stacks 2).length + 4)
    ⟨n, hn, by simpa [hstart, small] using ht⟩
  let b := embedState scanRegister scanPort a small
  refine ⟨m, hm, b, he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [b, small, scanPort, WeightScan.state] using
      embedState_stack scanRegister scanPort a small scanPort_injective 0
  · simpa [b, small, scanPort, WeightScan.state] using
      embedState_stack scanRegister scanPort a small scanPort_injective 1
  · have h := embedState_register scanRegister scanPort a small scanRegister_injective 3
    simpa [b, small, scanRegister, WeightScan.state, ha] using h
  · intro i hi2 hi6
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    fin_cases j <;> simp_all [scanPort]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [scanRegister] at hj <;> subst i <;> norm_num [Fin.coe_ofNat_eq_mod] at hi

abbrev emit : Cmd 8 7 :=
  .seq (pushConst 4 3 false) (.seq (escape emitPorts) (pushConst 4 3 true))
abbrev emittedState (a : Data) : Data :=
  pushedState 4 3 true (escapedState emitPorts (pushedState 4 3 false a))

theorem emit_eval (a : Data) :
    Eval emit (5 * (a.stacks 1).length + 7) a (emittedState a) := by
  have h := (pushConst_eval 4 3 false a).seq
    ((escape_eval_state emitPorts (pushedState 4 3 false a)).seq
      (pushConst_eval 4 3 true (escapedState emitPorts (pushedState 4 3 false a))))
  convert h using 1 ; simp [ emitPorts ] ; omega

abbrev copiedState (src dst : Fin 7) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none, SubexponentialSAT.StackRoutines.copyStacks src dst a.stacks⟩
abbrev clearedState (src : Fin 7) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none, SubexponentialSAT.StackRoutines.clearStacks src a.stacks⟩

abbrev callback : Cmd 8 7 :=
  .seq (.call (SubexponentialSAT.StackRoutines.copyProgram 1 2 3 3 4))
    (.seq (.call (SubexponentialSAT.StackRoutines.copyProgram 5 6 3 3 4))
      (.seq scan (.seq (.ite 6 emit (.call (SubexponentialSAT.StackRoutines.clearProgram 1 3 4)))
        (.call (SubexponentialSAT.StackRoutines.clearProgram 6 3 4)))))

def invariant (budget : List Bool) (a : Data) : Prop :=
  a.stacks 2 = [] ∧ a.stacks 3 = [] ∧ a.stacks 5 = budget ∧ a.stacks 6 = []
def keep (J : ℕ) (bits : List Bool) : Bool := decide (bits.count true < J)
def retain (J : ℕ) (bits out : List Bool) : List Bool :=
  if keep J bits then prependRecord bits out else out

theorem callback_contract (budget : List Bool) :
    SubexponentialSAT.RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (fun bits => 30 * (bits.length + budget.length + 1)) (invariant budget)
      (fun bits a b => b.stacks 4 = retain budget.length bits (a.stacks 4)) := by
  intro bits tail base hb
  let a := SubexponentialSAT.RecordPrograms.state ports base false true false tail bits.reverse
  let b := copiedState 1 2 a
  let d := copiedState 5 6 b
  have ha1 : a.stacks 1 = bits.reverse := by simp [a, ports, SubexponentialSAT.RecordPrograms.state]
  have ha3 : a.stacks 3 = [] := by simpa [a, ports, SubexponentialSAT.RecordPrograms.state] using hb.2.1
  have h1 := copy_eval 1 2 3 3 4 (by decide) (by decide) (by decide) (by decide) a ha3
  have hb3 : b.stacks 3 = [] := by simp [b, SubexponentialSAT.StackRoutines.copyStacks, ha3]
  have h2 := copy_eval 5 6 3 3 4 (by decide) (by decide) (by decide) (by decide) b hb3
  have hd2 : d.stacks 2 = bits.reverse := by
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks, hb.1]
  have hd6 : d.stacks 6 = budget := by
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks, hb.2.2]
  have hb5 : b.stacks 5 = budget := by
    simp [b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks, hb.2.2.1]
  obtain ⟨q, hq, c, hs, hc2, hc6, hcans, hcf, hcr⟩ := scan_eval d
  have hc1 : c.stacks 1 = bits.reverse := by
    rw [hcf 1 (by decide) (by decide)]
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks]
  have hc3 : c.stacks 3 = [] := by
    rw [hcf 3 (by decide) (by decide)]
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks, hb.2.1]
  have hc5 : c.stacks 5 = budget := by
    rw [hcf 5 (by decide) (by decide)]
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks, hb.2.2.1]
  have hc0 : c.stacks 0 = tail := by
    rw [hcf 0 (by decide) (by decide)]
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks]
  have hc4 : c.stacks 4 = base.stacks 4 := by
    rw [hcf 4 (by decide) (by decide)]
    simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, SubexponentialSAT.StackRoutines.copyStacks]
  have hr0 := hcr 0 (by decide)
  have hr1 := hcr 1 (by decide)
  have hr2 := hcr 2 (by decide)
  simp [d, b, a, ports, SubexponentialSAT.RecordPrograms.state, readRegs] at hr0 hr1 hr2
  rw [hd2, hd6, List.count_reverse] at hcans hc6
  have hclen : (c.stacks 6).length ≤ budget.length := by rw [hc6]; simp
  rw [hd2, List.length_reverse] at hq
  cases hp : keep budget.length bits with
  | false =>
      have ha : c.regs 6 = false := hcans.trans hp
      let e := clearedState 1 c
      let f := clearedState 6 e
      have h3 := clear_eval 1 3 4 c
      have h4 := clear_eval 6 3 4 e
      have hi : Eval (.ite 6 emit (.call (SubexponentialSAT.StackRoutines.clearProgram 1 3 4)))
          (2 * (c.stacks 1).length + 3 + 1) c e := .ite_false ha h3
      have he6 : e.stacks 6 = c.stacks 6 := by simp [e, SubexponentialSAT.StackRoutines.clearStacks]
      refine ⟨(7 * (a.stacks 1).length + 5) + ((7 * (b.stacks 5).length + 5) +
        (q + ((2 * (c.stacks 1).length + 3 + 1) + (2 * (e.stacks 6).length + 3)))),
        f, ?_, ?_, ?_, ?_⟩
      · rw [ha1, hb5, hc1, he6, List.length_reverse]
        dsimp only
        omega
      · simp [invariant, f, e, SubexponentialSAT.StackRoutines.clearStacks, hc2, hc3, hc5]
      · simp [retain, hp, f, e, SubexponentialSAT.StackRoutines.clearStacks, hc4]
      · have hf : SubexponentialSAT.RecordPrograms.state ports f false true false tail [] = f := by
          apply SubexponentialSAT.RecordPrograms.state_eq_self <;>
            simp [f, e, SubexponentialSAT.StackRoutines.clearStacks, ports, readRegs, hr0, hr1, hr2, hc0]
        rw [hf]
        exact h1.seq (h2.seq (hs.seq (hi.seq h4)))
  | true =>
      have ha : c.regs 6 = true := hcans.trans hp
      let e := emittedState c
      let f := clearedState 6 e
      have h3 := emit_eval c
      have h4 := clear_eval 6 3 4 e
      have hi : Eval (.ite 6 emit (.call (SubexponentialSAT.StackRoutines.clearProgram 1 3 4)))
          (5 * (c.stacks 1).length + 7 + 1) c e := .ite_true ha h3
      have he6 : e.stacks 6 = c.stacks 6 := by simp [e, emitPorts]
      refine ⟨(7 * (a.stacks 1).length + 5) + ((7 * (b.stacks 5).length + 5) +
        (q + ((5 * (c.stacks 1).length + 7 + 1) + (2 * (e.stacks 6).length + 3)))),
        f, ?_, ?_, ?_, ?_⟩
      · rw [ha1, hb5, hc1, he6, List.length_reverse]
        dsimp only
        omega
      · simp [invariant, f, e,
          emitPorts, SubexponentialSAT.StackRoutines.clearStacks, hc2, hc3, hc5]
      · simp [retain, hp, f, e,
          emitPorts, SubexponentialSAT.StackRoutines.clearStacks, hc1, hc4, prependRecord,
          frame_eq_escaped, List.append_assoc]
      · have hf : SubexponentialSAT.RecordPrograms.state ports f false true false tail [] = f := by
          apply SubexponentialSAT.RecordPrograms.state_eq_self <;>
            simp [f, e, emitPorts,
              SubexponentialSAT.StackRoutines.clearStacks, ports, readRegs, hr0, hr1, hr2, hc0]
        rw [hf]
        exact h1.seq (h2.seq (hs.seq (hi.seq h4)))

theorem fold_retain (J : ℕ) (words : List (List Bool)) (out : List Bool) :
    words.foldl (fun out bits => retain J bits out) out =
      appendEncoded ((words.filter (keep J)).reverse) out := by
  rw [← fold_prependRecord]
  induction words generalizing out with
  | nil => rfl
  | cons bits words ih =>
      cases hp : keep J bits <;> simp [retain, hp ] <;> exact ih _

abbrev command : Cmd 8 7 := SubexponentialSAT.RecordPrograms.iterate ports callback

def cost (budget : List Bool) (words : List (List Bool)) : ℕ :=
  3 + SubexponentialSAT.RecordPrograms.budget (fun bits => 30 * (bits.length + budget.length + 1)) words

theorem command_eval (budget : List Bool) (words accum : List (List Bool)) (base : Data)
    (hb : invariant budget base) (hin : base.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords words)
    (hpayload : base.stacks 1 = [])
    (hout : base.stacks 4 = SubexponentialSAT.ProgramEncoding.encodeRecords accum) :
    ∃ n next, n ≤ cost budget words ∧ invariant budget next ∧ next.stacks 0 = [] ∧
      next.stacks 1 = [] ∧
      next.stacks 4 = SubexponentialSAT.ProgramEncoding.encodeRecords
        ((words.filter (keep budget.length)).reverse ++ accum) ∧
      Eval command n base next := by
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    SubexponentialSAT.RecordPrograms.iterate_run_with ports callback (fun _ => false)
      (fun bits => 30 * (bits.length + budget.length + 1)) (invariant budget)
      (fun bits a b => b.stacks 4 = retain budget.length bits (a.stacks 4))
      (callback_contract budget) words [] base hb (base.regs 0) (base.regs 1) (base.regs 2)
  let final := SubexponentialSAT.RecordPrograms.state ports next false true false [] []
  have hstart : SubexponentialSAT.RecordPrograms.state ports base (base.regs 0) (base.regs 1)
      (base.regs 2) (SubexponentialSAT.Encoding.encodeList id words ++ []) [] = base := by
    apply SubexponentialSAT.RecordPrograms.state_eq_self <;>
      simp_all [ports, SubexponentialSAT.ProgramEncoding.encodeRecords]
  have hfold := history.fold_of_false (by simp) (fun s => s.stacks 4)
    (fun out bits => retain budget.length bits out) (fun _ _ _ h => h)
  rw [fold_retain, hout, appendEncoded_encodeRecords] at hfold
  refine ⟨n, final, hn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [invariant, final, SubexponentialSAT.RecordPrograms.state, ports] using hnext
  · simp [final, SubexponentialSAT.RecordPrograms.state, ports]
  · simp [final, SubexponentialSAT.RecordPrograms.state, ports]
  · simpa [final, SubexponentialSAT.RecordPrograms.state, ports] using hfold
  · have hany : words.any (fun _ => false) = false := by
      induction words <;> simp_all
    simpa only [hstart, hany, unread_false] using hiter

abbrev program := compiled command 0 4

theorem program_runsIn (budget : List Bool) (words accum : List (List Bool)) (base : Data)
    (hb : invariant budget base) (hin : base.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords words)
    (hpayload : base.stacks 1 = [])
    (hout : base.stacks 4 = SubexponentialSAT.ProgramEncoding.encodeRecords accum) :
    ∃ next, invariant budget next ∧ next.stacks 0 = [] ∧ next.stacks 1 = [] ∧
      next.stacks 4 = SubexponentialSAT.ProgramEncoding.encodeRecords
        ((words.filter (keep budget.length)).reverse ++ accum) ∧
      RunsIn program (cost budget words + 1)
        (base.withPC (some program.entry)) (next.withPC none) := by
  obtain ⟨n, next, hn, hi, h0, h1, h4, he⟩ := command_eval budget words accum base hb hin hpayload hout
  exact ⟨next, hi, h0, h1, h4, n + 1, Nat.add_le_add_right hn 1,
    compiled_halt_trace he 0 4⟩

theorem cost_bound (budget : List Bool) (words : List (List Bool)) (n : ℕ)
    (hlen : ∀ w ∈ words, w.length ≤ n) :
    cost budget words ≤ 3 + (36 * n + 30 * budget.length + 37) * words.length := by
  unfold cost
  apply Nat.add_le_add_left
  induction words with
  | nil => simp [SubexponentialSAT.RecordPrograms.budget]
  | cons w words ih =>
      have hw := hlen w (by simp)
      have ht := ih (fun x hx => hlen x (by simp [hx]))
      simp only [SubexponentialSAT.RecordPrograms.budget, List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.SupportProgram.Filter

end OAI.Algorithms
