import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramShiftSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def highRegs : Fin 4 → Fin 40 := Fin.castAdd 36
def highStacks : Fin 10 → Fin 896 := ![330,338,702,703,680,681,682,683,684,685]
def highChanged : List (Fin 896) := [702,703,680,681,682,683,684,685]

def highCommand : Code := .call (ProgramLinking.liftProgram
  LeafHighContextProgram.Local.program highRegs highStacks)
def highProgram := compiled highCommand 330 703

noncomputable def highResult (a : Data) (regs : Fin 4 → Bool) (high : List Bool) : Data :=
  embedState highRegs highStacks a (LeafHighContextProgram.Local.state regs
    (a.stacks 330) (a.stacks 338) (a.stacks 338).reverse
    (Restriction.zeroMerge (a.stacks 338) high).reverse [] [] [] [] [] [])

@[simp] theorem highResult_mask (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult a regs high).stacks 702 = (a.stacks 338).reverse :=
  embedState_stack highRegs highStacks a _ (by decide) 2

@[simp] theorem highResult_bits (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult a regs high).stacks 703 =
      (Restriction.zeroMerge (a.stacks 338) high).reverse :=
  embedState_stack highRegs highStacks a _ (by decide) 3

theorem highResult_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 896) (hi : i ∉ highChanged) :
    (highResult a regs high).stacks i = a.stacks i := by
  by_cases hx : ∃ j, highStacks j = i
  · obtain ⟨j,rfl⟩ := hx
    rw [show (highResult a regs high).stacks (highStacks j) =
      (LeafHighContextProgram.Local.state regs (a.stacks 330) (a.stacks 338)
        (a.stacks 338).reverse (Restriction.zeroMerge (a.stacks 338) high).reverse
        [] [] [] [] [] []).stacks j from
      embedState_stack highRegs highStacks a _ (by decide) j]
    fin_cases j <;> simp_all [highStacks,highChanged,LeafHighContextProgram.Local.state,
      LeafHighContextProgram.Local.tapes]
  · exact embedState_stack_frame highRegs highStacks a _ i hx

theorem highResult_register_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 40) (hi : 4 ≤ i.val) : (highResult a regs high).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

/-- The high vector is extracted from the actual encoded current tuple. Its
master counter and mask remain available for later odometer iterations. -/
theorem high_eval (a : Data) (words : List (List Bool)) (h : ℕ)
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (he : ∀ i ∈ highChanged, a.stacks i = [])
    (hshape : words.map List.length = List.replicate h 1)
    (hh : h = Restriction.highCount (a.stacks 338)) :
    ∃ steps regs, steps ≤ 22 * (a.stacks 338).length + 43 * h + 37 ∧
      Eval highCommand steps a (highResult a regs words.flatten) := by
  have hw : words.length = h := by
    have ht := congrArg List.length hshape
    simpa only [List.length_map,List.length_replicate] using ht
  have hf : words.flatten.length = h := by
    rw [List.length_flatten,hshape]
    simp
  have henc : (ProgramEncoding.encodeRecords words).length = 4*h+1 := by
    rw [show ProgramEncoding.encodeRecords words = Encoding.encodeList id words from rfl,
      ExecCNFTupleOdometer.encoded_length,hf,hw]
    omega
  obtain ⟨rf,⟨steps,hn,ht⟩⟩ := LeafHighContextProgram.Local.runsIn
    (a.regs ∘ highRegs) words (a.stacks 338) (hf.trans hh)
  have hp : projectState highRegs highStacks a =
      LeafHighContextProgram.Local.state (a.regs ∘ highRegs)
        (ProgramEncoding.encodeRecords words) (a.stacks 338) [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [highStacks,
        LeafHighContextProgram.Local.tapes,hc,
        he 702 (by simp [highChanged]),he 703 (by simp [highChanged]),
        he 680 (by simp [highChanged]),he 681 (by simp [highChanged]),
        he 682 (by simp [highChanged]),he 683 (by simp [highChanged]),
        he 684 (by simp [highChanged]),he 685 (by simp [highChanged])]
  rw [← hp] at ht
  have hex := eval_call_from_state LeafHighContextProgram.Local.program highRegs highStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  refine ⟨steps,rf,?_,?_⟩
  · unfold LeafHighContextProgram.Local.cost at hn
    rw [henc,hf,hw] at hn
    omega
  · simpa only [highCommand,highResult,hc] using hex

/-- Every source prefix of this polynomial local setup is bounded, including
all caller stacks. This does not charge space by the exponential outer run. -/
theorem high_trace_space (a : Data) (words : List (List Bool)) (h bound : ℕ)
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (he : ∀ i ∈ highChanged, a.stacks i = [])
    (hshape : words.map List.length = List.replicate h 1)
    (hh : h = Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∃ steps regs,
      Trace highProgram steps (a.withPC (some highProgram.entry))
        ((highResult a regs words.flatten).withPC none) ∧
      steps ≤ 65 * (a.stacks 338).length + 38 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace highProgram prefixSteps (a.withPC (some highProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * bound + 65 * (a.stacks 338).length + 38 := by
  obtain ⟨steps,regs,ht,heval⟩ := high_eval a words h hc he hshape hh
  have hdim : h ≤ (a.stacks 338).length := by
    rw [hh]
    exact List.length_filter_le _ _
  have htime : steps + 1 ≤ 65 * (a.stacks 338).length + 38 := by omega
  refine ⟨steps+1,regs,compiled_halt_trace heval 330 703,htime,?_⟩
  have hin : dataBits (a.withPC (some highProgram.entry)) ≤ 896 * bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound highProgram
    (steps := 65 * (a.stacks 338).length + 38) hin prefixSteps intermediate
    (hle.trans htime) htrace i
  simpa only [Nat.add_assoc] using hx

/-- The produced fixed-high values have their original ambient IDs. -/
theorem high_vector_semantics {n : ℕ} (H : Finset (Fin n)) (high : H → Bool) :
    (Restriction.zeroMerge (SqrtLogSpace.HighIncidenceProgram.descendingHighMask H)
      (List.ofFn (fun i => high (Order.highOrder H i)))).reverse =
      List.ofFn (HighIncidence.glue H high (fun _ => false)) := by
  let x := HighIncidence.glue H high (fun _ => false)
  have hhigh : List.ofFn (fun i => high (Order.highOrder H i)) =
      (Order.highCoordinates H).map x := by
    rw [← Order.highOrder_stream]
    congr 1
    funext i
    simp [x,HighIncidence.glue,(Order.highOrder H i).property]
  rw [hhigh]
  unfold SqrtLogSpace.HighIncidenceProgram.descendingHighMask Order.highCoordinates
  rw [Restriction.zeroMerge_map]
  have hx : (fun v => if decide (v ∈ H) then x v else false) = x := by
    funext v
    by_cases hv : v ∈ H <;> simp [hv,x,HighIncidence.glue]
  rw [hx,Order.coordinates_stream,List.reverse_reverse]

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def resetHigh : Code := .seq (.call (StackRoutines.clearProgram 702 0 1))
  (BankRoutines.clearCmd 702 0 1 highChanged)

def resetHighState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks highChanged a.stacks⟩

def resetHighCost (a : Data) :=
  2*(a.stacks 702).length+3+
    (2*(highChanged.map (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)).sum+27)

theorem resetHigh_eval (a : Data) : Eval resetHigh (resetHighCost a) a (resetHighState a) := by
  have h1 := BankRoutines.clear_call_eval (702 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (702 : Fin 896) (0 : Fin 40) 1 highChanged (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 702 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks highChanged (StackRoutines.clearStacks 702 a.stacks) =
      BankRoutines.clearBankStacks highChanged a.stacks := by
    funext i
    by_cases hi : i ∈ highChanged
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 702 := by intro h; subst i; exact hi (by simp [highChanged])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [resetHigh,resetHighCost,resetHighState,show highChanged.length=8 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem resetHigh_frame (a : Data) (i : Fin 896) (hi : i ∉ highChanged) :
    (resetHighState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i highChanged a.stacks hi

def prepareHigh : Code := .seq resetHigh highCommand
def prepareHighProgram := compiled prepareHigh 330 703

/-- This entry has no blank-buffer hypothesis: each repeated high branch pays
for cleanup before extracting the next assignment from its actual counter. -/
theorem prepareHigh_trace_space (a : Data) (words : List (List Bool)) (h bound : ℕ)
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (hshape : words.map List.length = List.replicate h 1)
    (hh : h = Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∃ steps regs,
      Trace prepareHighProgram steps (a.withPC (some prepareHighProgram.entry))
        ((highResult (resetHighState a) regs words.flatten).withPC none) ∧
      steps ≤ 18 * bound + 65 * (a.stacks 338).length + 68 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace prepareHighProgram prefixSteps (a.withPC (some prepareHighProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 914 * bound + 65 * (a.stacks 338).length + 68 := by
  have hc' : (resetHighState a).stacks 330 = ProgramEncoding.encodeRecords words :=
    (resetHigh_frame a 330 (by decide)).trans hc
  have hm : (resetHighState a).stacks 338 = a.stacks 338 := resetHigh_frame a 338 (by decide)
  obtain ⟨steps,regs,ht,he⟩ := high_eval (resetHighState a) words h hc'
    (fun i hi => BankRoutines.clearBankStacks_mem i highChanged a.stacks hi)
    hshape (by simpa only [hm] using hh)
  have hdim : h ≤ (a.stacks 338).length := by rw [hh]; exact List.length_filter_le _ _
  have hsum : (highChanged.map (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)).sum ≤ 8*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=702
      · subst i
        simp [StackRoutines.clearStacks]
      · simpa [StackRoutines.clearStacks,heq] using hb i)).trans_eq
    simp [highChanged]
  have hreset : resetHighCost a ≤ 18*bound+30 := by
    dsimp [resetHighCost]
    have := hb 702
    omega
  have htime : resetHighCost a + steps + 1 ≤ 18*bound+65*(a.stacks 338).length+68 := by
    rw [hm] at ht
    omega
  have heval := (resetHigh_eval a).seq he
  refine ⟨resetHighCost a+steps+1,regs,compiled_halt_trace heval 330 703,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareHighProgram.entry)) ≤ 896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound prepareHighProgram
    (steps := 18*bound+65*(a.stacks 338).length+68) hin prefixSteps intermediate
    (hle.trans htime) htrace i
  omega

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 4 5
abbrev Code := Cmd 4 5

def state (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) : Data :=
  ⟨regs,![mask,bits,rev,out,ones]⟩
def popped (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail bits rev out ones

def pop : Code := .base (.atom (.pop 0 0 1))
def keep : Code := .seq (.base (.atom (.push 2 2))) (.base (.atom (.push 4 3)))
def drop : Code := .seq (.base (.atom (.copy 2 2))) (.base (.atom (.copy 3 3)))
def body : Code := .seq (.base (.atom (.pop 1 2 3))) (.seq (.ite 0 keep drop) pop)
def loop : Code := .while 1 body
def command : Code := .seq pop (.seq loop (.call (transferProgram 2 3 0 1)))
def program := compiled command 0 3

theorem pop_eval (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) :
    Eval pop 1 (state regs mask bits rev out ones) (popped regs mask bits rev out ones) := by
  convert Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 5) (0 : Fin 4) 1)
    (state regs mask bits rev out ones)) using 1
  · rfl
  · apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> rfl

theorem iteration (regs : Fin 4 → Bool) (b x : Bool) (mask bits rev out ones : List Bool) :
    ∃ rf, Eval body 5 (popped regs (b::mask) (x::bits) rev out ones)
      (popped rf mask bits (if b then x::rev else rev) out (if b then true::ones else ones)) := by
  let a := popped regs (b::mask) (x::bits) rev out ones
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 (some x)
  have hp : Eval (.base (.atom (.pop (1 : Fin 5) (2 : Fin 4) 3))) 1 a
      (state r mask bits rev out ones) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 5) (2 : Fin 4) 3) a) using 1
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [a, popped, state, readRegs,
      StructuredProgram.Atom.instr, execInstr]
  have hs : Eval (.ite (0 : Fin 4) keep drop) 3 (state r mask bits rev out ones)
      (state r mask bits (if b then x::rev else rev) out (if b then true::ones else ones)) := by
    cases b with
    | false =>
        apply Eval.ite_false (by simp [r,readRegs,state])
        have h := (Eval.base (StructuredProgram.Eval.atom (.copy (2 : Fin 4) 2)
          (state r mask bits rev out ones))).seq
          (Eval.base (StructuredProgram.Eval.atom (.copy (3 : Fin 4) 3) _))
        simpa [drop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,execInstr] using h
    | true =>
        apply Eval.ite_true (by simp [r,readRegs,state])
        have h := (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 5) (2 : Fin 4))
          (state r mask bits rev out ones))).seq
          (Eval.base (StructuredProgram.Eval.atom (.push (4 : Fin 5) (3 : Fin 4)) _))
        convert h using 1
        · rfl
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;> simp [state, r, readRegs, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  exact ⟨r,hp.seq (hs.seq (pop_eval r mask bits
    (if b then x::rev else rev) out (if b then true::ones else ones)))⟩

theorem loop_eval (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool)
    (hlen : mask.length=bits.length) :
    ∃ rf, Eval loop (6*mask.length+1) (popped regs mask bits rev out ones)
      (state rf [] [] ((Restriction.selected true mask bits).reverse++rev) out
        (List.replicate (Restriction.highCount mask) true++ones)) := by
  induction mask generalizing regs bits rev ones with
  | nil =>
      have he : bits=[] := List.eq_nil_of_length_eq_zero hlen.symm
      subst bits
      exact ⟨readRegs regs 0 1 none,Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases bits with
      | nil => simp at hlen
      | cons x bits =>
          obtain ⟨ri,hi⟩ := iteration regs b x mask bits rev out ones
          obtain ⟨rf,hr⟩ := ih ri bits (if b then x::rev else rev)
            (if b then true::ones else ones) (by simpa using hlen)
          have h := Eval.while_true (show (popped regs (b::mask) (x::bits) rev out ones).regs 1=true by rfl) hi hr
          have hlen' : mask.length = bits.length := by simpa using hlen
          refine ⟨rf,?_⟩
          cases b with
          | false =>
              convert h using 1
              · rfl
              · simp only [List.length_cons] at *
                omega
              · simp [Restriction.selected, Restriction.highCount,
                  Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
          | true =>
              convert h using 1
              · rfl
              · simp only [List.length_cons] at *
                omega
              · simp [Restriction.selected, Restriction.highCount,
                  Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful,
                  List.reverse_cons, List.append_assoc, List.replicate_succ']

theorem command_eval (regs : Fin 4 → Bool) (mask bits : List Bool)
    (hlen : mask.length=bits.length) :
    ∃ rf, Eval command (6*mask.length+3*Restriction.highCount mask+5)
      (state regs mask bits [] [] [])
      (state rf [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)) := by
  obtain ⟨rs,hl⟩ := loop_eval regs mask bits [] [] [] hlen
  simp only [List.append_nil] at hl
  have ht := ListRegisterProgram.transfer_run (2 : Fin 5) 3 (0 : Fin 4) 1
    (by decide) (by decide) rs
    (state rs [] [] (Restriction.selected true mask bits).reverse []
      (List.replicate (Restriction.highCount mask) true)).stacks
  have hs : transferStacks 2 3
      (state rs [] [] (Restriction.selected true mask bits).reverse []
        (List.replicate (Restriction.highCount mask) true)).stacks =
      (state (readRegs rs 0 1 none) [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)).stacks := by
    funext i; fin_cases i <;> simp [transferStacks,state]
  have hc : Eval (.call (transferProgram (2 : Fin 5) 3 (0 : Fin 4) 1))
      (3*Restriction.highCount mask+3)
      (state rs [] [] (Restriction.selected true mask bits).reverse []
        (List.replicate (Restriction.highCount mask) true))
      (state (readRegs rs 0 1 none) [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)) := by
    apply Eval.call
    change Trace _ (3*(Restriction.selected true mask bits).reverse.length+3) _ _ at ht
    rw [hs] at ht
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state,
      Restriction.highCount, List.length_reverse,
      Restriction.selected_true_length mask bits hlen] using ht
  refine ⟨readRegs rs 0 1 none,?_⟩
  convert (pop_eval regs mask bits [] [] []).seq (hl.seq hc) using 1
  · rfl
  · omega

end HeadSelect

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def regs : Fin 4 → Fin 40 := Fin.castAdd 36
def stackMap : Fin 5 → Fin 896 := ![879,878,877,867,868]
def changed : List (Fin 896) := [867,868,877,878,879,880]
def copy (src dst : Fin 896) : Code := .call (copyProgram src dst 880 0 1)
def select : Code := .call (ProgramLinking.liftProgram HeadSelect.program regs stackMap)
def command : Code := .seq (copy 858 878) (.seq (copy 670 879) select)
def program := compiled command 858 867

def copied (a : Data) : Data :=
  ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
    copyStacks 670 879 (copyStacks 858 878 a.stacks)⟩

noncomputable def result (a : Data) (rf : Fin 4 → Bool) : Data :=
  embedState regs stackMap (copied a) (HeadSelect.state rf [] [] []
    (Restriction.selected true (a.stacks 670) (a.stacks 858))
    (List.replicate (Restriction.highCount (a.stacks 670)) true))

@[simp] theorem result_E (a : Data) (rf : Fin 4 → Bool) :
    (result a rf).stacks 867 = Restriction.selected true (a.stacks 670) (a.stacks 858) :=
  embedState_stack regs stackMap (copied a) _ (by decide) 3

@[simp] theorem result_H (a : Data) (rf : Fin 4 → Bool) :
    (result a rf).stacks 868 = List.replicate (Restriction.highCount (a.stacks 670)) true :=
  embedState_stack regs stackMap (copied a) _ (by decide) 4

theorem result_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896)
    (hi : i ∉ changed) : (result a rf).stacks i = a.stacks i := by
  have hn : ¬ ∃ j, stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i = (copied a).stacks i from
    embedState_stack_frame regs stackMap (copied a) _ i hn]
  have h1 : i ≠ 879 := by intro he; subst i; simp [changed] at hi
  have h2 : i ≠ 878 := by intro he; subst i; simp [changed] at hi
  simp [copied,copyStacks,h1,h2]

theorem command_eval (a : Data)
    (he : ∀ i ∈ changed, a.stacks i=[])
    (hlen : (a.stacks 670).length=(a.stacks 858).length) :
    ∃ rf, Eval command (20*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+16)
      a (result a rf) := by
  have ht : a.stacks 880=[] := he 880 (by simp [changed])
  have h1 : Eval (copy 858 878) (7*(a.stacks 858).length+5) a
      ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩ :=
    .call _ (ListRegisterProgram.copy_run 858 878 880 0 1 (by decide) (by decide)
      (by decide) (by decide) a.regs a.stacks ht)
  have h2 : Eval (copy 670 879) (7*(a.stacks 670).length+5)
      ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩ (copied a) := by
    apply Eval.call
    simpa only [copied, StackRoutines.readRegs_reset,
      copyStacks_frame 858 878 670 a.stacks (by decide)] using
      ListRegisterProgram.copy_run (670 : Fin 896) 879 880 (0 : Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        (readRegs a.regs 0 1 none) (copyStacks 858 878 a.stacks)
        (by simpa only [copyStacks_frame 858 878 880 a.stacks (by decide)] using ht)
  have hp : projectState regs stackMap (copied a) =
      HeadSelect.state ((copied a).regs ∘ regs) (a.stacks 670) (a.stacks 858) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [copied, stackMap, copyStacks,
        he 867 (by simp [changed]),he 868 (by simp [changed]),he 877 (by simp [changed]),
        he 878 (by simp [changed]),he 879 (by simp [changed])]
  obtain ⟨rf,hs⟩ := HeadSelect.command_eval ((copied a).regs ∘ regs)
    (a.stacks 670) (a.stacks 858) hlen
  have hx := compiled_halt_trace hs 0 3
  rw [← hp] at hx
  have h3 := eval_call_from_state HeadSelect.program regs stackMap (copied a)
    (Fin.castAdd_injective _ _) (by decide) hx
  refine ⟨rf,?_⟩
  have hh := h1.seq (h2.seq h3)
  rw [← hlen] at hh
  convert hh using 1
  · rfl
  · omega
  · rfl

/-- Head selection is a complete physical scan over ambient coordinates and
preserves every caller stack except its six documented output/work ports. -/
theorem trace_space (a : Data) (bound : ℕ)
    (he : ∀ i ∈ changed, a.stacks i=[])
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ rf, Trace program steps (a.withPC (some program.entry)) ((result a rf).withPC none) ∧
      steps ≤ 23*bound+17 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤919*bound+17 := by
  obtain ⟨rf,hs⟩ := command_eval a he hlen
  have hh : Restriction.highCount (a.stacks 670)≤(a.stacks 670).length :=
    List.length_filter_le _ _
  have ht : 20*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+16+1≤23*bound+17 := by
    have := hb 670
    omega
  refine ⟨_,rf,compiled_halt_trace hs 858 867,ht,?_⟩
  have hin : dataBits (a.withPC (some program.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound program (steps:=23*bound+17) hin
    prefixSteps intermediate (Nat.le_trans hle ht) htrace i
  omega

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def reset : Code := .seq (.call (StackRoutines.clearProgram 880 0 1))
  (BankRoutines.clearCmd 880 0 1 changed)

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩

def resetCost (a : Data) :=
  2*(a.stacks 880).length+3+
    (2*(changed.map (fun i => ((StackRoutines.clearStacks 880 a.stacks) i).length)).sum+21)

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (880 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (880 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 880 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (StackRoutines.clearStacks 880 a.stacks) =
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i ∈ changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 880 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=6 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi


def prepare : Code := .seq reset command
def prepareProgram := compiled prepare 858 867

/-- Repeated calls pay to discard every old output and work buffer before the
new head projection. The only input shape condition is equal ambient lengths. -/
theorem prepare_trace_space (a : Data) (bound : ℕ)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ rf, Trace prepareProgram steps (a.withPC (some prepareProgram.entry))
      ((result (resetState a) rf).withPC none) ∧ steps ≤ 37*bound+41 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace prepareProgram prefixSteps (a.withPC (some prepareProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤933*bound+41 := by
  have hm : (resetState a).stacks 670=a.stacks 670 := reset_frame a 670 (by decide)
  have he : (resetState a).stacks 858=a.stacks 858 := reset_frame a 858 (by decide)
  obtain ⟨rf,hs⟩ := command_eval (resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i changed a.stacks hi)
    (by simpa only [hm,he] using hlen)
  have hsum : (changed.map (fun i => ((clearStacks 880 a.stacks) i).length)).sum≤6*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=880
      · subst i
        simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have hc : resetCost a≤14*bound+24 := by
    dsimp [resetCost]
    have := hb 880
    omega
  have hh : Restriction.highCount (a.stacks 670)≤(a.stacks 670).length :=
    List.length_filter_le _ _
  have htime : resetCost a+(20*((resetState a).stacks 670).length+
      3*Restriction.highCount ((resetState a).stacks 670)+16)+1≤37*bound+41 := by
    rw [hm]
    have := hb 670
    omega
  have hx := (reset_eval a).seq hs
  refine ⟨_,rf,compiled_halt_trace hx 858 867,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareProgram.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hbound := StructuredSpace.local_stack_bound prepareProgram (steps:=37*bound+41) hin
    prefixSteps intermediate (Nat.le_trans hle htime) htrace i
  omega

@[simp] theorem prepared_E (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 867=Restriction.selected true (a.stacks 670) (a.stacks 858) := by
  rw [result_E,reset_frame a 670 (by decide),reset_frame a 858 (by decide)]

@[simp] theorem prepared_H (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 868=List.replicate (Restriction.highCount (a.stacks 670)) true := by
  rw [result_H,reset_frame a 670 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

end NativeHeadSelect

/-- Durable outer high counter and exact-count accumulator. Query reconstruction
returns its whole conditioned count on323, which the real adder consumes. -/
def highPorts : LeafBranchProgram.Ports 40 896 where
  counter := {
    register := ⟨fun i => ⟨19+i.val,by omega⟩,
      by intro i j h; apply Fin.ext; simpa using congrArg Fin.val h⟩
    counter := 789
    scratch := 790
    counter_ne_scratch := by decide }
  mass := {
    register := Fin.castAdd 32
    stack := ![788,323,791]
    register_injective := Fin.castAdd_injective 8 32
    stack_injective := by decide }
  disjoint_counter := by decide
  disjoint_scratch := by decide

/-- A callback is entered only under a true iterator guard; restoring that
known control bit is an actual source instruction after conditioned readback. -/
def restoreHighGuard : Code := .base (.atom (.set 21 true))
theorem restoreHighGuard_eval (a : Data) : Eval restoreHighGuard 1 a
    ⟨Function.update a.regs 21 true,a.stacks⟩ :=
  .base (StructuredProgram.Eval.atom (.set 21 true) a)

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copyHighCounter : Code := .seq (.call (clearProgram 330 0 1))
  (.seq (.call (clearProgram 792 0 1)) (.call (copyProgram 789 330 792 0 1)))

def copiedHighCounter (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 330 (a.stacks 789)) 792 []⟩

def copyHighCost (a : Data) : ℕ :=
  2*(a.stacks 330).length+2*(a.stacks 792).length+7*(a.stacks 789).length+11

theorem copyHighCounter_eval (a : Data) :
    Eval copyHighCounter (copyHighCost a) a (copiedHighCounter a) := by
  have h1 := BankRoutines.clear_call_eval (330 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1
    (readRegs a.regs 0 1 none) (clearStacks 330 a.stacks)
  have h3 : Eval (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1))
      (7*(a.stacks 789).length+5)
      ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
        clearStacks 792 (clearStacks 330 a.stacks)⟩
      ⟨readRegs (readRegs (readRegs a.regs 0 1 none) 0 1 none) 0 1 none,
        copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks))⟩ := by
    apply Eval.call
    simpa only [clearStacks_frame 330 789 a.stacks (by decide),
      clearStacks_frame 792 789 (clearStacks 330 a.stacks) (by decide)] using
      ListRegisterProgram.copy_run (789 : Fin 896) 330 792 (0 : Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        (readRegs (readRegs a.regs 0 1 none) 0 1 none)
        (clearStacks 792 (clearStacks 330 a.stacks)) (by simp)
  have hs : copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks)) =
      Function.update (Function.update a.stacks 330 (a.stacks 789)) 792 [] := by
    funext i
    by_cases h330 : i=330
    · subst i
      simp [copyStacks,clearStacks]
    · by_cases h792 : i=792
      · subst i
        simp [copyStacks,clearStacks]
      · simp [copyStacks,clearStacks,h330,h792]
  have hx := h1.seq (h2.seq h3)
  simp only [clearStacks_frame 330 792 a.stacks (by decide),hs,readRegs_reset] at hx
  convert hx using 1
  · rfl
  · dsimp [copyHighCost]
    omega
  · rfl

@[simp] theorem copiedHighCounter_word (a : Data) :
    (copiedHighCounter a).stacks 330=a.stacks 789 := by simp [copiedHighCounter]

theorem copiedHighCounter_frame (a : Data) (i : Fin 896) (h330 : i≠330) (h792 : i≠792) :
    (copiedHighCounter a).stacks i=a.stacks i := by simp [copiedHighCounter,h330,h792]

theorem copiedHighCounter_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((copiedHighCounter a).stacks i).length≤bound := by
  intro i
  by_cases h792 : i=792
  · subst i; simp [copiedHighCounter]
  · by_cases h330 : i=330
    · subst i; simpa using hb 789
    · simpa [copiedHighCounter,h330,h792] using hb i

def prepareBranch : Code := .seq copyHighCounter (.call prepareHighProgram)
def prepareBranchProgram := compiled prepareBranch 789 703

/-- The high assignment comes from the durable outer odometer. Its paid copy
into the old lower context is temporary; all later lower query routines may
reuse330 without changing the live outer iterator789. -/
theorem prepareBranch_trace_space (a : Data) (words : List (List Bool)) (h bound : ℕ)
    (hc : a.stacks 789=ProgramEncoding.encodeRecords words)
    (hshape : words.map List.length=List.replicate h 1)
    (hh : h=Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ regs, Trace prepareBranchProgram steps (a.withPC (some prepareBranchProgram.entry))
      ((highResult (resetHighState (copiedHighCounter a)) regs words.flatten).withPC none) ∧
      steps≤29*bound+65*(a.stacks 338).length+80 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace prepareBranchProgram prefixSteps (a.withPC (some prepareBranchProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤925*bound+65*(a.stacks 338).length+80 := by
  have hm : (copiedHighCounter a).stacks 338=a.stacks 338 :=
    copiedHighCounter_frame a 338 (by decide) (by decide)
  obtain ⟨steps,regs,ht,hbound,_⟩ := prepareHigh_trace_space (copiedHighCounter a)
    words h bound (by simpa only [copiedHighCounter_word] using hc) hshape
    (by simpa only [hm] using hh) (copiedHighCounter_bound a bound hb)
  rw [hm] at hbound
  have hcopy : copyHighCost a≤11*bound+11 := by
    dsimp [copyHighCost]
    have := hb 330
    have := hb 792
    have := hb 789
    omega
  have htime : copyHighCost a+steps+1≤29*bound+65*(a.stacks 338).length+80 := by omega
  have heval := (copyHighCounter_eval a).seq (Eval.call _ ht)
  refine ⟨_,regs,compiled_halt_trace heval 789 703,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareBranchProgram.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound prepareBranchProgram
    (steps:=29*bound+65*(a.stacks 338).length+80) hin prefixSteps intermediate
    (Nat.le_trans hle htime) htrace i
  omega

@[simp] theorem preparedBranch_mask (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult (resetHighState (copiedHighCounter a)) regs high).stacks 702=
      (a.stacks 338).reverse := by
  rw [highResult_mask,resetHigh_frame _ 338 (by decide),
    copiedHighCounter_frame a 338 (by decide) (by decide)]

@[simp] theorem preparedBranch_high (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult (resetHighState (copiedHighCounter a)) regs high).stacks 703=
      (Restriction.zeroMerge (a.stacks 338) high).reverse := by
  rw [highResult_bits,resetHigh_frame _ 338 (by decide),
    copiedHighCounter_frame a 338 (by decide) (by decide)]

theorem preparedBranch_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 896) (hi : i∉highChanged) (h330 : i≠330) (h792 : i≠792) :
    (highResult (resetHighState (copiedHighCounter a)) regs high).stacks i=a.stacks i := by
  rw [highResult_frame _ _ _ i hi,resetHigh_frame _ i hi,
    copiedHighCounter_frame a i h330 h792]

namespace CanonicalHigh
open DisjointReuse

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def regMap : Fin 3 → Fin 40 := Fin.castAdd 37
def stackMap : Fin 3 → Fin 896 := ![788,793,794]
def command : Code := .call (ProgramLinking.liftProgram
  CanonicalWordProgram.normalizeUnsignedProgram regMap stackMap)

noncomputable def result (a : Data) : Data := embedState regMap stackMap a
  (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
    (binaryNat (CounterPrograms.value (a.stacks 788))) [])

@[simp] theorem result_count (a : Data) : (result a).stacks 788=
    countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  change (result a).stacks (stackMap 0) =
    countWord (BinaryArithmetic.toNat (a.stacks 788))
  have h := embedState_stack regMap stackMap a
    (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
      (binaryNat (CounterPrograms.value (a.stacks 788))) []) (by decide) 0
  simpa [result, CanonicalWordProgram.state,
    CounterPrograms.value_eq_toNat, binaryNat, countWord] using h

theorem result_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result a).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,rfl⟩
  fin_cases j <;> simp_all [stackMap]

theorem command_eval (a : Data) (h793 : a.stacks 793=[]) (h794 : a.stacks 794=[]) :
    ∃ steps, steps≤17*(a.stacks 788).length+29 ∧ Eval command steps a (result a) := by
  obtain ⟨steps,hbound,he⟩ := CanonicalWordProgram.normalizeUnsigned_eval
    (a.regs ∘ regMap) (a.stacks 788)
  have hp : projectState regMap stackMap a =
      CanonicalWordProgram.state (a.regs ∘ regMap) (a.stacks 788) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [stackMap, h793, h794]
  have ht := compiled_halt_trace he 0 0
  rw [← hp] at ht
  exact ⟨steps+1,by omega,eval_call_from_state CanonicalWordProgram.normalizeUnsignedProgram
    regMap stackMap a (Fin.castAdd_injective _ _) (by decide) ht⟩

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def reset : Code := .seq (.call (clearProgram 793 0 1)) (.call (clearProgram 794 0 1))
def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,clearStacks 794 (clearStacks 793 a.stacks)⟩

theorem reset_eval (a : Data) :
    Eval reset (2*(a.stacks 793).length+2*(a.stacks 794).length+6) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (793 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_call_eval (794 : Fin 896) (0 : Fin 40) 1
    (readRegs a.regs 0 1 none) (clearStacks 793 a.stacks)
  have h := h1.seq h2
  simp only [clearStacks_frame 793 794 a.stacks (by decide),readRegs_reset] at h
  convert h using 1
  · rfl
  · omega
  · rfl

def prepare : Code := .seq reset command
def program := compiled prepare 788 788

/-- Canonicalizes the actual complete high accumulator on the same bounded
source run. Zero is the singleton false word, never an empty output. -/
theorem trace_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), Trace program steps (a.withPC (some program.entry))
      ((result (resetState a)).withPC none) ∧ steps≤21*bound+36 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤917*bound+36 := by
  have hm : (resetState a).stacks 788=a.stacks 788 := by simp [resetState,clearStacks]
  obtain ⟨steps,hbound,he⟩ := command_eval (resetState a)
    (by simp [resetState,clearStacks]) (by simp [resetState,clearStacks])
  rw [hm] at hbound
  have ht : (2*(a.stacks 793).length+2*(a.stacks 794).length+6)+steps+1≤21*bound+36 := by
    have := hb 793
    have := hb 794
    have := hb 788
    omega
  have hx := (reset_eval a).seq he
  refine ⟨_,compiled_halt_trace hx 788 788,ht,?_⟩
  have hin : dataBits (a.withPC (some program.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hspace := StructuredSpace.local_stack_bound program (steps:=21*bound+36) hin
    prefixSteps intermediate (Nat.le_trans hle ht) htrace i
  omega

@[simp] theorem final_count (a : Data) : (result (resetState a)).stacks 788=
    countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  rw [result_count]
  simp [resetState,clearStacks]

theorem final_width (a : Data) (n : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788)≤2^n) :
    ((result (resetState a)).stacks 788).length≤n+1 := by
  rw [final_count]
  exact countWord_length_le hcount

theorem final_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result (resetState a)).stacks i=a.stacks i := by
  rw [result_frame _ i h788 h793 h794]
  simp [resetState,clearStacks,h793,h794]

end CanonicalHigh

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 8 12
abbrev Code := Cmd 8 12

def state (regs : Fin 8 → Bool) (bits mask baseline u v x y z tmp full out low : List Bool) : Data :=
  ⟨regs,![bits,mask,baseline,u,v,x,y,z,tmp,full,out,low]⟩

def copy (src dst : Fin 12) : Code := .call (copyProgram src dst 8 0 1)
def smallRegs : Fin 4 → Fin 8 := Fin.castAdd 4
def expandStacks : Fin 4 → Fin 12 := ![6,5,11,7]
def expand : Code := .call (ProgramLinking.liftProgram Restriction.program smallRegs expandStacks)
def transfer : Code := .call (transferProgram 7 9 0 1)
def mergeStacks : Fin 10 → Fin 12 := ![9,1,2,3,4,5,6,7,8,10]
def merge : Code := .call (ProgramLinking.liftProgram LeafAssignmentMergeProgram.Native.program id mergeStacks)
def clear : Code := .call (clearProgram 9 0 1)
def command : Code := .seq (copy 0 5) (.seq (copy 1 6)
  (.seq expand (.seq transfer (.seq merge clear))))
def program := compiled command 0 10

private theorem copy_eval (src dst : Fin 12) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 12) ≠ dst)
    (a : Data) (ht : a.stacks 8 = []) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a
      ⟨readRegs a.regs 0 1 none,copyStacks src dst a.stacks⟩ := by
  exact .call _ (ListRegisterProgram.copy_run src dst 8 0 1 hsd hst htd (by decide)
    a.regs a.stacks ht)

private theorem expand_frame (bits mask baseline u v out : List Bool)
    (i : Fin 12) (hi : ¬∃ j, expandStacks j=i) :
    (![bits,mask,baseline,u,v,[],[],out,[],[],[],[]] : Fin 12 → List Bool) i =
      ![bits,mask,baseline,u,v,bits,mask,[],[],[],[],[]] i := by
  have h5 : i≠5 := by intro h; exact hi ⟨1,h.symm⟩
  have h6 : i≠6 := by intro h; exact hi ⟨0,h.symm⟩
  have h7 : i≠7 := by intro h; exact hi ⟨3,h.symm⟩
  fin_cases i <;> simp_all

private theorem merge_frame (bits mask baseline u v full out : List Bool)
    (i : Fin 12) (hi : ¬∃ j, mergeStacks j=i) :
    (![bits,mask,baseline,u,v,[],[],[],[],full,out,[]] : Fin 12 → List Bool) i =
      ![bits,mask,baseline,u,v,[],[],[],[],full,[],[]] i := by
  have h10 : i≠10 := by intro h; exact hi ⟨9,h.symm⟩
  fin_cases i <;> simp_all

theorem expand_eval (regs : Fin 8 → Bool) (bits mask baseline u v : List Bool)
    (hh : bits.length = Restriction.highCount mask) :
    ∃ (rf : Fin 8 → Bool), Eval expand (5*mask.length+3)
      (state regs bits mask baseline u v bits mask [] [] [] [] [])
      (state rf bits mask baseline u v [] [] (Restriction.zeroMerge mask bits).reverse [] [] [] []) := by
  let a := state regs bits mask baseline u v bits mask [] [] [] [] []
  obtain ⟨rs,hl⟩ := Restriction.zero_loop_eval (regs ∘ smallRegs) mask bits [] hh
  have he := (Restriction.popMask_eval (regs ∘ smallRegs) mask bits [] []).seq hl
  have ht : Trace Restriction.program (5*mask.length+3)
      ((Restriction.state (regs ∘ smallRegs) mask bits [] []).withPC
        (some Restriction.program.entry))
      ((Restriction.state rs [] [] [] (Restriction.zeroMerge mask bits).reverse).withPC none) := by
    have hn : 1 + (5*mask.length+1) + 1 = 5*mask.length+3 := by omega
    simpa only [Restriction.program, Restriction.command, List.append_nil, hn] using
      compiled_halt_trace he 0 3
  have hp : projectState smallRegs expandStacks a =
      Restriction.state (regs ∘ smallRegs) mask bits [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hp] at ht
  have hx := eval_call_from_state Restriction.program smallRegs expandStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  let rf : Fin 8 → Bool := fun i => if h : i.val < 4 then rs ⟨i.val,h⟩ else regs i
  have hb : embedState smallRegs expandStacks a
      (Restriction.state rs [] [] [] (Restriction.zeroMerge mask bits).reverse) =
      state rf bits mask baseline u v [] [] (Restriction.zeroMerge mask bits).reverse [] [] [] [] := by
    apply embedState_eq_of_ports smallRegs expandStacks a _ _
      (Fin.castAdd_injective _ _) (by decide)
    · intro i
      simp [state,rf,smallRegs,i.isLt,Restriction.state]
    · intro i hi
      have hn : ¬i.val<4 := by
        intro hh
        exact hi ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
      simp [state,rf,hn,a]
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact expand_frame bits mask baseline u v _ i hi
  refine ⟨rf,?_⟩
  simpa only [expand, hb] using hx

theorem transfer_eval (regs : Fin 8 → Bool) (bits mask baseline u v full : List Bool) :
    Eval transfer (3*full.length+3)
      (state regs bits mask baseline u v [] [] full.reverse [] [] [] [])
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] full [] []) := by
  have h := ListRegisterProgram.transfer_run (7 : Fin 12) 9 (0 : Fin 8) 1
    (by decide) (by decide) regs
    (state regs bits mask baseline u v [] [] full.reverse [] [] [] []).stacks
  apply Eval.call
  have hs : transferStacks 7 9 (state regs bits mask baseline u v [] [] full.reverse [] [] [] []).stacks =
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] full [] []).stacks := by
    funext i; fin_cases i <;> simp [transferStacks,state]
  change Trace _ (3*full.reverse.length+3) _ _ at h
  rw [hs] at h
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, state,
    List.length_reverse] using h

theorem merge_eval (regs : Fin 8 → Bool) (bits mask baseline u v full : List Bool)
    (hm : full.length = mask.length) (hb : full.length = baseline.length) :
    ∃ rf, Eval merge (30*full.length+22)
      (state regs bits mask baseline u v [] [] [] [] full [] [])
      (state rf bits mask baseline u v [] [] [] [] full
        (LeafAssignmentMergeProgram.merge full mask baseline) []) := by
  let a := state regs bits mask baseline u v [] [] [] [] full [] []
  obtain ⟨rf,ht⟩ := LeafAssignmentMergeProgram.Native.program_trace regs full mask baseline u v hm hb
  have hp : projectState id mergeStacks a =
      LeafAssignmentMergeProgram.Native.data regs full mask baseline u v [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hp] at ht
  have hx := eval_call_from_state LeafAssignmentMergeProgram.Native.program id mergeStacks a
    Function.injective_id (by decide) ht
  have he : embedState id mergeStacks a
      (LeafAssignmentMergeProgram.Native.data rf full mask baseline u v [] [] []
        (LeafAssignmentMergeProgram.merge full mask baseline)) =
      state rf bits mask baseline u v [] [] [] [] full
        (LeafAssignmentMergeProgram.merge full mask baseline) [] := by
    apply embedState_eq_of_ports id mergeStacks a _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      exact merge_frame bits mask baseline u v full _ i hi
  exact ⟨rf,by simpa only [merge,he] using hx⟩

theorem clear_eval (regs : Fin 8 → Bool) (bits mask baseline u v full out : List Bool) :
    Eval clear (2*full.length+3)
      (state regs bits mask baseline u v [] [] [] [] full out [])
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] [] out []) := by
  have h := ListRegisterProgram.clear_run (9 : Fin 12) (0 : Fin 8) 1 regs
    (state regs bits mask baseline u v [] [] [] [] full out []).stacks
  apply Eval.call
  have hs : clearStacks 9 (state regs bits mask baseline u v [] [] [] [] full out []).stacks =
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] [] out []).stacks := by
    funext i; fin_cases i <;> simp [clearStacks,state]
  change Trace (clearProgram 9 0 1) (2*full.length+3) _ _ at h
  rw [hs] at h
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, state] using h

/-- Compressed h-bit head assignments are expanded and merged physically;
all masters survive, and every temporary is empty on return. -/
theorem command_eval (regs : Fin 8 → Bool) (bits mask baseline u v : List Bool)
    (hh : bits.length = Restriction.highCount mask) (hm : mask.length = baseline.length) :
    ∃ rf, Eval command (7*bits.length+47*mask.length+41)
      (state regs bits mask baseline u v [] [] [] [] [] [] [])
      (state rf bits mask baseline u v [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge mask bits) mask baseline) []) := by
  have h1 := copy_eval 0 5 (by decide) (by decide) (by decide)
    (state regs bits mask baseline u v [] [] [] [] [] [] []) rfl
  have h1' : Eval (copy 0 5) (7*bits.length+5)
      (state regs bits mask baseline u v [] [] [] [] [] [] [])
      (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] []) := by
    convert h1 using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [copyStacks, state]
  have h2 := copy_eval 1 6 (by decide) (by decide) (by decide)
    (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] []) rfl
  have h2' : Eval (copy 1 6) (7*mask.length+5)
      (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] [])
      (state (readRegs (readRegs regs 0 1 none) 0 1 none) bits mask baseline u v bits mask [] [] [] [] []) := by
    convert h2 using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [copyStacks, state]
  obtain ⟨r3,h3⟩ := expand_eval (readRegs (readRegs regs 0 1 none) 0 1 none) bits mask baseline u v hh
  have hlen : (Restriction.zeroMerge mask bits).length = mask.length :=
    (Restriction.zeroMerge_spec mask bits hh).1
  have h4 := transfer_eval r3 bits mask baseline u v (Restriction.zeroMerge mask bits)
  obtain ⟨r5,h5⟩ := merge_eval (readRegs r3 0 1 none) bits mask baseline u v (Restriction.zeroMerge mask bits)
    hlen (hlen.trans hm)
  have h6 := clear_eval r5 bits mask baseline u v (Restriction.zeroMerge mask bits)
    (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge mask bits) mask baseline)
  refine ⟨readRegs r5 0 1 none,?_⟩
  have hx := h1'.seq (h2'.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [hlen] at hx
  convert hx using 1
  · rfl
  · omega

/-- The same overlay run has linear local time and a bound on every prefix
of every stack, including arbitrary preserved words u and v. -/
theorem trace_space (regs : Fin 8 → Bool) (bits mask baseline u v : List Bool)
    (hh : bits.length = Restriction.highCount mask) (hm : mask.length = baseline.length)
    (bound : ℕ) (hmask : mask.length ≤ bound) (hu : u.length ≤ bound) (hv : v.length ≤ bound) :
    ∃ rf, Trace program (7*bits.length+47*mask.length+42)
      ((state regs bits mask baseline u v [] [] [] [] [] [] []).withPC (some program.entry))
      ((state rf bits mask baseline u v [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge mask bits) mask baseline) []).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 7*bits.length+47*mask.length+42 →
        Trace program prefixSteps
          ((state regs bits mask baseline u v [] [] [] [] [] [] []).withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 66*bound+42 := by
  obtain ⟨rf,he⟩ := command_eval regs bits mask baseline u v hh hm
  have hbits : bits.length ≤ mask.length := by rw [hh]; exact List.length_filter_le _ _
  refine ⟨rf,compiled_halt_trace he 0 10,?_⟩
  have hin : dataBits ((state regs bits mask baseline u v [] [] [] [] [] [] []).withPC
      (some program.entry)) ≤ 12*bound := by
    apply StreamResources.dataBits_le_mul
    intro i
    clear he rf
    fin_cases i <;> simp [state] <;> omega
  intro prefixSteps intermediate hle htrace i
  have ht : prefixSteps ≤ 54*bound+42 := by omega
  have hb := StructuredSpace.local_stack_bound program (steps := 54*bound+42) hin
    prefixSteps intermediate ht htrace i
  omega

/-- On an actual ambient assignment, extraction followed by expansion and
overlay changes precisely the selected head coordinates. -/
theorem overlay_selected (mask current baseline : List Bool)
    (hc : mask.length = current.length) (hb : mask.length = baseline.length) :
    LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge mask (Restriction.selected true mask current)) mask baseline =
      LeafAssignmentMergeProgram.merge current mask baseline := by
  induction mask generalizing current baseline with
  | nil =>
      have he : current=[] := List.eq_nil_of_length_eq_zero hc.symm
      simp [he,Restriction.zeroMerge,Restriction.merge,LeafAssignmentMergeProgram.merge]
  | cons b mask ih =>
      cases current with
      | nil => simp at hc
      | cons x current =>
          cases baseline with
          | nil => simp at hb
          | cons y baseline =>
              cases b <;> simp [Restriction.zeroMerge,Restriction.merge,Restriction.selected,
                LeafAssignmentMergeProgram.merge,ih current baseline (by simpa using hc) (by simpa using hb)]

theorem overlay_ofFn {n : ℕ} (head current baseline : Fin n → Bool) :
    LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (List.ofFn head)
        (Restriction.selected true (List.ofFn head) (List.ofFn current)))
      (List.ofFn head) (List.ofFn baseline) =
      List.ofFn (fun v => if head v then current v else baseline v) := by
  rw [overlay_selected _ _ _ (by simp) (by simp),LeafAssignmentMergeProgram.merge_ofFn]

end Overlay

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def regMap : Fin 8 → Fin 40 := Fin.castAdd 32
def stackMap : Fin 12 → Fin 896 := ![859,670,869,870,871,872,873,874,875,876,145,877]
def changed : List (Fin 896) := [145,872,873,874,875,876,877]
def command : Code := .call (ProgramLinking.liftProgram Overlay.program regMap stackMap)
def program := compiled command 859 145

noncomputable def result (a : Data) (rf : Fin 8 → Bool) : Data :=
  embedState regMap stackMap a (Overlay.state rf (a.stacks 859) (a.stacks 670)
    (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
    (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
      (a.stacks 670) (a.stacks 869)) [])

@[simp] theorem result_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result a rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) :=
  embedState_stack regMap stackMap a _ (by decide) 10

theorem result_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  by_cases hn : ∃ j, stackMap j=i
  · obtain ⟨j,rfl⟩ := hn
    rw [show (result a rf).stacks (stackMap j)=
      (Overlay.state rf (a.stacks 859) (a.stacks 670)
        (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
          (a.stacks 670) (a.stacks 869)) []).stacks j from
      embedState_stack regMap stackMap a _ (by decide) j]
    fin_cases j <;> simp_all [stackMap,changed,Overlay.state]
  · exact embedState_stack_frame regMap stackMap a _ i hn

theorem command_eval (a : Data) (he : ∀ i∈changed, a.stacks i=[])
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length) :
    ∃ rf, Eval command (7*(a.stacks 859).length+47*(a.stacks 670).length+42)
      a (result a rf) := by
  have hp : projectState regMap stackMap a = Overlay.state (a.regs ∘ regMap)
      (a.stacks 859) (a.stacks 670) (a.stacks 869) (a.stacks 870) (a.stacks 871)
      [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [stackMap,
        he 145 (by simp [changed]),he 872 (by simp [changed]),he 873 (by simp [changed]),
        he 874 (by simp [changed]),he 875 (by simp [changed]),he 876 (by simp [changed]),
        he 877 (by simp [changed])]
  obtain ⟨rf,hs⟩ := Overlay.command_eval (a.regs ∘ regMap)
    (a.stacks 859) (a.stacks 670) (a.stacks 869) (a.stacks 870) (a.stacks 871) hh hm
  have ht := compiled_halt_trace hs 0 10
  rw [← hp] at ht
  exact ⟨rf,eval_call_from_state Overlay.program regMap stackMap a
    (Fin.castAdd_injective _ _) (by decide) ht⟩

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def reset : Code := .seq (.call (StackRoutines.clearProgram 875 0 1))
  (BankRoutines.clearCmd 875 0 1 changed)

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩

def resetCost (a : Data) :=
  2*(a.stacks 875).length+3+
    (2*(changed.map (fun i => ((StackRoutines.clearStacks 875 a.stacks) i).length)).sum+24)

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (875 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (875 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 875 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (StackRoutines.clearStacks 875 a.stacks) =
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i ∈ changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 875 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=7 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi



def prepare : Code := .seq reset command
def prepareProgram := compiled prepare 859 145

/-- Every raw head candidate is expanded in ambient order and overlaid onto
the retained tuple/high baseline by an actual bounded-memory routine. -/
theorem prepare_trace_space (a : Data) (bound : ℕ)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ rf, Trace prepareProgram steps (a.withPC (some prepareProgram.entry))
      ((result (resetState a) rf).withPC none) ∧ steps≤70*bound+70 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace prepareProgram prefixSteps (a.withPC (some prepareProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤966*bound+70 := by
  have hbits : (resetState a).stacks 859=a.stacks 859 := reset_frame a 859 (by decide)
  have hmask : (resetState a).stacks 670=a.stacks 670 := reset_frame a 670 (by decide)
  have hbase : (resetState a).stacks 869=a.stacks 869 := reset_frame a 869 (by decide)
  obtain ⟨rf,hs⟩ := command_eval (resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i changed a.stacks hi)
    (by simpa only [hbits,hmask] using hh) (by simpa only [hmask,hbase] using hm)
  have hsum : (changed.map (fun i => ((clearStacks 875 a.stacks) i).length)).sum≤7*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=875
      · subst i
        simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have hc : resetCost a≤16*bound+27 := by
    dsimp [resetCost]
    have := hb 875
    omega
  have htime : resetCost a+(7*((resetState a).stacks 859).length+
      47*((resetState a).stacks 670).length+42)+1≤70*bound+70 := by
    rw [hbits,hmask]
    have := hb 859
    have := hb 670
    omega
  have hx := (reset_eval a).seq hs
  refine ⟨_,rf,compiled_halt_trace hx 859 145,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareProgram.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hbound := StructuredSpace.local_stack_bound prepareProgram (steps:=70*bound+70) hin
    prefixSteps intermediate (Nat.le_trans hle htime) htrace i
  omega

@[simp] theorem prepared_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result (resetState a) rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) := by
  rw [result_assignment,reset_frame a 670 (by decide),reset_frame a 859 (by decide),
    reset_frame a 869 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

theorem prepared_scratch (a : Data) (rf : Fin 8 → Bool) (i : Fin 896)
    (hi : i∈([872,873,874,875,876,877] : List (Fin 896))) :
    (result (resetState a) rf).stacks i=[] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 5
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 6
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 7
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 8
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 9
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 11

theorem prepared_length (a : Data) (rf : Fin 8 → Bool)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670)) :
    ((result (resetState a) rf).stacks 145).length=(a.stacks 670).length := by
  rw [prepared_assignment,LeafAssignmentMergeProgram.merge_length]
  exact (Restriction.zeroMerge_spec _ _ hh).1

/-- The return-state envelope is unchanged across arbitrarily many tuple/head
visits. The larger local prefix bound is not fed back as a new input size. -/
theorem prepared_bound (a : Data) (rf : Fin 8 → Bool) (bound : ℕ)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((result (resetState a) rf).stacks i).length≤bound := by
  intro i
  by_cases hc : i=145
  · subst i
    rw [prepared_length _ _ hh]
    exact hb 670
  · by_cases hs : i∈([872,873,874,875,876,877] : List (Fin 896))
    · rw [prepared_scratch _ _ _ hs]
      exact Nat.zero_le _
    · rw [prepared_frame _ _ i (by simpa [changed,hc] using hs)]
      exact hb i

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
