import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI BitProgram StructuredCalls

namespace CountFalse

abbrev Data := State 3 2

def state (regs : Fin 3 → Bool) (mask out : List Bool) : Data :=
  ⟨regs, fun i => if i = 0 then mask else out⟩

def ports : UnaryForPrograms.Ports 3 2 := ⟨0,0,1⟩

def body : Cmd 3 2 :=
  .ite 0 (.base .skip) (.base (.atom (.push 1 2)))

def command : Cmd 3 2 :=
  .seq (.base (.atom (.set 2 true))) (UnaryForPrograms.forCmd ports body)

def program := compiled command 0 1

theorem popped_state (regs : Fin 3 → Bool) (mask out : List Bool) :
    UnaryForPrograms.popped ports (state regs mask out) =
      state (readRegs regs 0 1 mask.head?) mask.tail out := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ports, state]

theorem body_eval (regs : Fin 3 → Bool) (mask out : List Bool) (b : Bool)
    (hbit : regs 0 = b) (hone : regs 2 = true) :
    Eval body (if b then 1 else 2) (state regs mask out)
      (state regs mask (if b then out else true :: out)) := by
  cases b with
  | true => exact .ite_true hbit (.base (.skip _))
  | false =>
      apply Eval.ite_false hbit
      convert Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) (2 : Fin 3))
        (state regs mask out)) using 1
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i
        fin_cases i <;> simp [state, StructuredProgram.Atom.instr, execInstr, hone]

/-- Each actual mask pop charges one constant-cost branch; the mathematical
visit list is proof data and is absent from all executable stacks. -/
theorem visits (mask out : List Bool) (regs : Fin 3 → Bool) (hone : regs 2 = true) :
    ∃ costs ticks rf, ticks ≤ 4 * mask.length + 2 ∧ rf 2 = true ∧
      UnaryForPrograms.Visits ports body costs ticks (state regs mask out)
        (state rf [] (List.replicate (mask.countP (!·)) true ++ out)) := by
  induction mask generalizing regs out with
  | nil =>
      refine ⟨[],2,readRegs regs 0 1 none,by simp,?_,?_⟩
      · simp [readRegs, hone]
      · simpa only [popped_state, List.head?_nil, List.tail_nil, List.countP_nil,
          List.replicate_zero, List.nil_append] using
          UnaryForPrograms.Visits.done (p:=ports) (body:=body) (state regs [] out) rfl
  | cons b mask ih =>
      let r := readRegs regs 0 1 (some b)
      have hr : r 2 = true := by simp [r, readRegs, hone]
      let next := if b then out else true :: out
      obtain ⟨costs,ticks,rf,ht,hf,hv⟩ := ih next r hr
      have he := body_eval r mask out b (by simp [r, readRegs]) hr
      have hstep := UnaryForPrograms.Visits.step (p:=ports) (body:=body)
        (d:=state regs (b::mask) out) (by simp [state, ports])
        (by simpa only [popped_state, List.head?_cons, List.tail_cons] using he)
        (by simp [state, ports, UnaryForPrograms.popped]) hv
      refine ⟨(if b then 1 else 2)::costs, (if b then 1 else 2)+ticks+2, rf, ?_, hf, ?_⟩
      · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
      · have hword : List.replicate ((b::mask).countP (!·)) true ++ out =
            List.replicate (mask.countP (!·)) true ++ next := by
          cases b <;> simp [next, List.replicate_succ', List.append_assoc]
        rw [hword]
        exact hstep

theorem command_eval (mask out : List Bool) (regs : Fin 3 → Bool) :
    ∃ ticks rf, ticks ≤ 4 * mask.length + 3 ∧
      Eval command ticks (state regs mask out)
        (state rf [] (List.replicate (mask.countP (!·)) true ++ out)) := by
  let r := Function.update regs 2 true
  obtain ⟨costs,ticks,rf,ht,_,hv⟩ := visits mask out r (by simp [r])
  have hs : Eval (.base (.atom (.set (2 : Fin 3) true))) 1
      (state regs mask out) (state r mask out) := .base (.atom _ _)
  exact ⟨1+ticks,rf,by omega,hs.seq hv.eval⟩

/-- Exact unary false-count and every source-prefix bound on one fixed local
program. Its input and output words both have at most the incoming mask size. -/
theorem trace_space (mask : List Bool) (regs : Fin 3 → Bool) :
    ∃ ticks rf, ticks ≤ 4 * mask.length + 4 ∧
      Trace program ticks ((state regs mask []).withPC (some program.entry))
        ((state rf [] (List.replicate (mask.countP (!·)) true)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace program prefixSteps ((state regs mask []).withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 6 * mask.length + 4 := by
  obtain ⟨ticks,rf,ht,he⟩ := command_eval mask [] regs
  have htime : ticks+1 ≤ 4*mask.length+4 := by omega
  refine ⟨ticks+1,rf,htime,?_,?_⟩
  · simpa only [program, List.append_nil] using compiled_halt_trace he 0 1
  · have hi : dataBits ((state regs mask []).withPC (some program.entry)) ≤ 2*mask.length := by
      apply StreamResources.dataBits_le_mul
      intro i
      fin_cases i <;> simp [state]
    intro prefixSteps intermediate hp ht i
    have hb := StructuredSpace.local_stack_bound program hi prefixSteps intermediate
      (hp.trans htime) ht i
    omega

end CountFalse


open SubexpSetupStorage
abbrev Data := State 16 896
abbrev Command := Cmd 16 896

def scratch : List (Fin 896) := [325,326,327,328,329]

def countRegister (i : Fin 3) : Fin 16 := i.castLE (by decide)
def countStack (i : Fin 2) : Fin 896 := if i = 0 then 325 else 326

theorem countRegister_injective : Function.Injective countRegister := Fin.castLE_injective (by decide)
theorem countStack_injective : Function.Injective countStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countStack]

def countCommand : Command :=
  isolated CountFalse.program countRegister countStack 329 scratch [(338,325)] [(326,832)]

def countPrepared (a : Data) : Data := prepareState 329 scratch [(338,325)] a

noncomputable def countMiddle (a : Data) (rf : Fin 3 → Bool) : Data :=
  embedState countRegister countStack (countPrepared a)
    (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))

noncomputable def countResult (a : Data) (rf : Fin 3 → Bool) : Data :=
  finishState scratch [(326,832)] (countMiddle a rf)

theorem countPrepared_stack (a : Data) (i : Fin 896) :
    (countPrepared a).stacks i =
      if i = 325 then a.stacks 338 else if i ∈ scratch then [] else a.stacks i := by
  simp only [countPrepared, prepareState, beforeCopies, copyManyState, copyState_stack,
    resetMany_stacks, clearMany_stacks]
  by_cases h : i = 325
  · subst i
    simp [scratch]
  · by_cases hi : i=329 <;> simp [h, hi, scratch, clearMany_stacks]

theorem countMiddle_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (countMiddle a rf).stacks i =
      if i = 326 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i ∈ scratch then [] else a.stacks i := by
  by_cases h0 : i = 325
  · subst i
    have h := embedState_stack countRegister countStack (countPrepared a)
      (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
      countStack_injective 0
    simpa [countMiddle, countStack, CountFalse.state, scratch] using h
  · by_cases h1 : i = 326
    · subst i
      have h := embedState_stack countRegister countStack (countPrepared a)
        (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
        countStack_injective 1
      simpa [countMiddle, countStack, CountFalse.state] using h
    · rw [countMiddle, embedState_stack_frame, countPrepared_stack]
      · simp [h0,h1]
      · rintro ⟨j,hj⟩
        fin_cases j <;> simp [countStack] at hj <;> simp_all

theorem countResult_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (countResult a rf).stacks i =
      if i = 832 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [countResult, finishState, resetMany_stacks, clearMany_stacks,
    copyManyState, copyState_stack, List.map_cons, List.map_nil]
  by_cases h : i ∈ scratch
  · have hi : i ≠ 832 := by intro he; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h
    simp [h,hi]
  · by_cases hi : i=832
    · subst i; simp [countMiddle_stack, scratch]
    · have h326 : i ≠ 326 := by intro he; subst i; exact h (by simp [scratch])
      simp [h, hi, h326, clearMany_stacks, countMiddle_stack]

theorem countCommand_eval (a : Data) :
    ∃ ticks rf, ticks ≤ prepareCost 329 scratch [(338,325)] a +
        (4 * (a.stacks 338).length + 4 + finishCost scratch [(326,832)] (countMiddle a rf)) ∧
      Eval countCommand ticks a (countResult a rf) := by
  have hp : project countRegister countStack (countPrepared a) =
      CountFalse.state ((countPrepared a).regs ∘ countRegister) (a.stacks 338) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [Function.comp_apply, countStack, countPrepared_stack, scratch]
  obtain ⟨ticks,rf,ht,htrace,_⟩ := CountFalse.trace_space (a.stacks 338)
    ((countPrepared a).regs ∘ countRegister)
  rw [← hp] at htrace
  have he := isolated_eval CountFalse.program countRegister countStack
    countRegister_injective countStack_injective 329 scratch [(338,325)] [(326,832)] a
    (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
    (by simp) (by simp) (by rintro ⟨j,hj⟩; fin_cases j <;> norm_num [countStack, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hj)
    (by simpa only [countPrepared] using htrace)
  exact ⟨_,rf,by dsimp only [countMiddle, countPrepared]; omega,he⟩

/-- This setup is polynomial local work, so charging its entire finite run is
valid for all-prefix storage. It never charges a surrounding pair traversal. -/
theorem countCommand_cost (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B)
    (rf : Fin 3 → Bool) :
    prepareCost 329 scratch [(338,325)] a +
        (4 * (a.stacks 338).length + 4 + finishCost scratch [(326,832)] (countMiddle a rf)) ≤
      100 * (B+1) := by
  have hm := hb 338
  have hc : ((a.stacks 338).countP (!·)) ≤ B := List.countP_le_length.trans hm
  have h0 := clearManyCost_le [329] a B hb
  have h1 : ∀ i, ((clearManyState [329] a).stacks i).length ≤ B := by
    intro i
    rw [clearMany_stacks]
    split <;> simp_all
  have h2 := clearManyCost_le scratch (clearManyState [329] a) B h1
  have h3 : ∀ i, ((countMiddle a rf).stacks i).length ≤ B := by
    intro i
    rw [countMiddle_stack]
    split_ifs <;> simp_all
  have h4 := clearManyCost_le [832] (countMiddle a rf) B h3
  have h5 : ∀ i,
      ((copyManyState [(326,832)] (clearManyState [832] (countMiddle a rf))).stacks i).length ≤ B := by
    intro i
    simp only [copyManyState, copyState_stack, clearMany_stacks]
    by_cases h : i=832
    · subst i
      simpa [countMiddle_stack, scratch] using hc
    · simp [h, h3, clearMany_stacks]
  have h6 := clearManyCost_le scratch
    (copyManyState [(326,832)] (clearManyState [832] (countMiddle a rf))) B h5
  simp only [prepareCost, finishCost, List.map_cons, List.map_nil,
    copyManyCost, Nat.add_zero]
  have hp : (beforeCopies 329 scratch a).stacks 338 = a.stacks 338 := by
    simp [beforeCopies, resetMany_stacks, clearMany_stacks, scratch]
  rw [hp]
  have hout : (clearManyState [832] (countMiddle a rf)).stacks 326 =
      List.replicate ((a.stacks 338).countP (!·)) true := by
    simp [clearMany_stacks, countMiddle_stack]
  rw [hout, List.length_replicate]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, one_mul] at h0 h4
  have hs : scratch.length = 5 := rfl
  rw [hs] at h2 h6
  omega



/-- The real descending high mask has exactly one false bit per residual
coordinate, including both empty-coordinate edge cases. -/
theorem false_count_highMask {n : ℕ} (H : Finset (Fin n)) :
    (HighIncidenceProgram.descendingHighMask H).countP (!·) = n-H.card := by
  rw [HighIncidenceProgram.descendingHighMask, List.countP_map]
  have hp : (fun v : Fin n => !(decide (v ∈ H))) = (fun v => decide (v ∉ H)) := by
    funext v
    simp
  change (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates n).countP (fun v => !(decide (v ∈ H))) = _
  rw [hp]
  change ((List.finRange n).reverse).countP (fun v => decide (v ∉ H)) = _
  rw [List.countP_reverse, List.countP_eq_length_filter]
  exact HighIncidenceProgram.freeCoordinates_length H

def setupCommand : Command :=
  .seq countCommand (.seq (clearMany [833,834,835]) (copyCmd 243 833 329))

noncomputable def setupResult (a : Data) (rf : Fin 3 → Bool) : Data :=
  copyState 243 833 (clearManyState [833,834,835] (countResult a rf))

theorem setupResult_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (setupResult a rf).stacks i =
      if i=832 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i=833 then a.stacks 243
      else if i ∈ scratch ∨ i=834 ∨ i=835 then [] else a.stacks i := by
  simp only [setupResult, copyState_stack, clearMany_stacks]
  by_cases h833 : i=833
  · subst i
    simp [countResult_stack, scratch]
  · simp [h833, clearMany_stacks, countResult_stack, scratch]
    split_ifs <;> simp_all

theorem setupCommand_eval (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ ticks rf, ticks ≤ 120*(B+1) ∧ Eval setupCommand ticks a (setupResult a rf) := by
  obtain ⟨ticks,rf,ht,he⟩ := countCommand_eval a
  have ht' := ht.trans (countCommand_cost a B hb rf)
  have hm : ((a.stacks 338).countP (!·)) ≤ B := List.countP_le_length.trans (hb 338)
  have hc : ∀ i, ((countResult a rf).stacks i).length ≤ B := by
    intro i
    rw [countResult_stack]
    split_ifs <;> simp_all
  have hclear := clearMany_eval [833,834,835] (countResult a rf)
  have hcost := clearManyCost_le [833,834,835] (countResult a rf) B hc
  have htmp : (clearManyState [833,834,835] (countResult a rf)).stacks 329 = [] := by
    simp [clearMany_stacks, countResult_stack, scratch]
  have hcopy := copy_eval (243:Fin 896) 833 329
    (clearManyState [833,834,835] (countResult a rf)) (by decide) (by decide) (by decide) htmp
  have hsrc : (clearManyState [833,834,835] (countResult a rf)).stacks 243 = a.stacks 243 := by
    simp [clearMany_stacks, countResult_stack, scratch]
  refine ⟨_,rf,?_,he.seq (hclear.seq hcopy)⟩
  rw [hsrc]
  have hj := hb 243
  simp only [List.length_cons, List.length_nil] at hcost
  omega

/-- Both pair controllers are initialized by executed scans/copies. All
persistent caller ports outside the finite written set are preserved. -/
theorem setup_resources {n : ℕ} (a : Data) (H : Finset (Fin n)) (J B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hj : a.stacks 243 = List.replicate J true)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : Data), ticks ≤ 120*(B+1)+1 ∧
      Trace (compiled setupCommand 338 832) ticks
        (a.withPC (some (compiled setupCommand 338 832).entry)) (b.withPC none) ∧
      b.stacks 832 = List.replicate (n-H.card) true ∧
      b.stacks 833 = List.replicate J true ∧ b.stacks 834 = [] ∧ b.stacks 835 = [] ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠832 → i≠833 → i≠834 → i≠835 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled setupCommand 338 832) prefixSteps
          (a.withPC (some (compiled setupCommand 338 832).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+120*(B+1)+1 := by
  obtain ⟨ticks,rf,ht,he⟩ := setupCommand_eval a B hb
  refine ⟨ticks+1,setupResult a rf,by omega,compiled_halt_trace he 338 832,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupResult_stack,hm,false_count_highMask]
  · simp [setupResult_stack,hj]
  · simp [setupResult_stack]
  · simp [setupResult_stack]
  · intro i hi
    have h832 : i≠832 := by intro h; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    have h833 : i≠833 := by intro h; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    simp [setupResult_stack,h832,h833,hi]
  · intro i hi h832 h833 h834 h835
    simp [setupResult_stack,hi,h832,h833,h834,h835]
  · have hmass : dataBits (a.withPC (some (compiled setupCommand 338 832).entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled setupCommand 338 832)
      hmass prefixSteps intermediate (hp.trans (show ticks+1 ≤120*(B+1)+1 by omega)) htrace i
    omega



def fillRegister (i : Fin 4) : Fin 16 := i.castLE (by decide)
def fillStack (i : Fin 4) : Fin 896 := ⟨325+i.val, by omega⟩
def fillInput (isE : Bool) : Fin 896 := if isE then 834 else 835
def fillOutput (isE : Bool) : Fin 896 := if isE then 858 else 857

theorem fillRegister_injective : Function.Injective fillRegister := Fin.castLE_injective (by decide)
theorem fillStack_injective : Function.Injective fillStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [fillStack] at he
  omega

def fillCommand (isE : Bool) : Command :=
  isolated OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program fillRegister fillStack 329 scratch
    [(338,325),(fillInput isE,327)] [(328,fillOutput isE)]

def fillPrepared (isE : Bool) (a : Data) : Data :=
  prepareState 329 scratch [(338,325),(fillInput isE,327)] a

noncomputable def fillMiddle (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool) : Data :=
  embedState fillRegister fillStack (fillPrepared isE a)
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] [] word)

noncomputable def fillResult (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool) : Data :=
  finishState scratch [(328,fillOutput isE)] (fillMiddle isE a rf word)

theorem fillPrepared_stack (isE : Bool) (a : Data) (i : Fin 896) :
    (fillPrepared isE a).stacks i =
      if i=325 then a.stacks 338 else if i=327 then a.stacks (fillInput isE)
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [fillPrepared, prepareState, beforeCopies, copyManyState, copyState_stack,
    resetMany_stacks, clearMany_stacks]
  by_cases h325 : i=325
  · subst i; cases isE <;> simp [fillInput,scratch,clearMany_stacks]
  · by_cases h327 : i=327
    · subst i; cases isE <;> simp [fillInput,scratch,clearMany_stacks]
    · by_cases h329 : i=329 <;> cases isE <;>
        simp [fillInput,h325,h327,h329,scratch,clearMany_stacks]

theorem fillMiddle_stack (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool)
    (i : Fin 896) :
    (fillMiddle isE a rf word).stacks i =
      if i=328 then word else if i ∈ scratch then [] else a.stacks i := by
  by_cases hi : ∃ j, fillStack j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [fillMiddle, embedState_stack _ _ _ _ fillStack_injective]
    fin_cases j <;> simp [fillStack, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state, scratch]
  · have hframe := embedState_stack_frame fillRegister fillStack (fillPrepared isE a)
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] [] word) i hi
    rw [show (fillMiddle isE a rf word).stacks i = (fillPrepared isE a).stacks i from hframe,
      fillPrepared_stack]
    have h325 : i≠325 := by intro h; exact hi ⟨0,h.symm⟩
    have h327 : i≠327 := by intro h; exact hi ⟨2,h.symm⟩
    have h328 : i≠328 := by intro h; exact hi ⟨3,h.symm⟩
    simp [h325,h327,h328]

theorem fillResult_stack (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool)
    (i : Fin 896) :
    (fillResult isE a rf word).stacks i =
      if i=fillOutput isE then word else if i ∈ scratch then [] else a.stacks i := by
  simp only [fillResult, finishState, resetMany_stacks, clearMany_stacks,
    copyManyState, copyState_stack, List.map_cons, List.map_nil]
  by_cases hs : i ∈ scratch
  · have ho : i≠fillOutput isE := by
      intro h
      subst i
      cases isE <;> norm_num [fillOutput,scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hs
    simp [hs,ho]
  · have h328 : i≠328 := by intro h; subst i; exact hs (by simp [scratch])
    by_cases ho : i=fillOutput isE
    · subst i
      cases isE <;> simp [fillOutput,fillMiddle_stack,scratch]
    · cases isE <;> simp_all [fillOutput,fillMiddle_stack,scratch,clearMany_stacks]

theorem fillCommand_eval {n : ℕ} (isE : Bool) (a : Data) (H : Finset (Fin n))
    (bits : Fin (n-H.card) → Bool)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hb : a.stacks (fillInput isE) = (List.ofFn bits).reverse) :
    ∃ rf, Eval (fillCommand isE)
      (prepareCost 329 scratch [(338,325),(fillInput isE,327)] a +
        (5*n+3+finishCost scratch [(328,fillOutput isE)]
          (fillMiddle isE a rf (List.ofFn (HighIncidenceProgram.freeFill H bits)))))
      a (fillResult isE a rf (List.ofFn (HighIncidenceProgram.freeFill H bits))) := by
  have hp : project fillRegister fillStack (fillPrepared isE a) =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state
        ((fillPrepared isE a).regs ∘ fillRegister)
        (HighIncidenceProgram.descendingHighMask H) [] (List.ofFn bits).reverse [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [Function.comp_apply, fillStack, fillPrepared_stack,
        scratch, hm, hb, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  obtain ⟨rf,htrace,_⟩ := HighIncidenceProgram.freeFill_trace_space
    ((fillPrepared isE a).regs ∘ fillRegister) H bits
  rw [← hp] at htrace
  refine ⟨rf,?_⟩
  exact isolated_eval OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program fillRegister fillStack
    fillRegister_injective fillStack_injective 329 scratch
    [(338,325),(fillInput isE,327)] [(328,fillOutput isE)] a
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
      (List.ofFn (HighIncidenceProgram.freeFill H bits)))
    (by cases isE <;> simp [fillInput]) (by cases isE <;> simp [fillOutput])
    (by rintro ⟨j,hj⟩; have he:=congrArg Fin.val hj; have hjlt:=j.isLt; simp [fillStack] at he; omega)
    (by simpa only [fillPrepared] using htrace)



theorem fillCommand_cost (isE : Bool) (a : Data) (B n : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (rf : Fin 4 → Bool)
    (word : List Bool) (hw : word.length ≤ n) :
    prepareCost 329 scratch [(338,325),(fillInput isE,327)] a +
        (5*n+3+finishCost scratch [(328,fillOutput isE)] (fillMiddle isE a rf word)) ≤
      100*(B+n+1) := by
  have h0 := clearManyCost_le [329] a B hb
  have h1 : ∀ i, ((clearManyState [329] a).stacks i).length ≤ B := by
    intro i
    rw [clearMany_stacks]
    split <;> simp_all
  have h2 := clearManyCost_le scratch (clearManyState [329] a) B h1
  have h3 : ∀ i, ((fillMiddle isE a rf word).stacks i).length ≤ B+n := by
    intro i
    rw [fillMiddle_stack]
    split_ifs
    · exact hw.trans (Nat.le_add_left n B)
    · exact Nat.zero_le _
    · exact (hb i).trans (Nat.le_add_right B n)
  have h4 := clearManyCost_le [fillOutput isE] (fillMiddle isE a rf word) (B+n) h3
  have h5 : ∀ i,
      ((copyManyState [(328,fillOutput isE)]
        (clearManyState [fillOutput isE] (fillMiddle isE a rf word))).stacks i).length ≤ B+n := by
    intro i
    simp only [copyManyState, copyState_stack, clearMany_stacks]
    by_cases h : i=fillOutput isE
    · subst i
      cases isE <;> simp [fillOutput, fillMiddle_stack]
      all_goals omega
    · simp [h,clearMany_stacks,h3]
  have h6 := clearManyCost_le scratch
    (copyManyState [(328,fillOutput isE)]
      (clearManyState [fillOutput isE] (fillMiddle isE a rf word))) (B+n) h5
  simp only [prepareCost, finishCost, List.map_cons, List.map_nil,
    copyManyCost, Nat.add_zero]
  have hp0 : (beforeCopies 329 scratch a).stacks 338 = a.stacks 338 := by
    simp [beforeCopies,resetMany_stacks,clearMany_stacks,scratch]
  have hp1 : (copyState 338 325 (beforeCopies 329 scratch a)).stacks (fillInput isE) =
      a.stacks (fillInput isE) := by
    cases isE <;> simp [copyState_stack,fillInput,beforeCopies,resetMany_stacks,clearMany_stacks,scratch]
  have hout : (clearManyState [fillOutput isE] (fillMiddle isE a rf word)).stacks 328 = word := by
    cases isE <;> simp [clearMany_stacks,fillOutput,fillMiddle_stack]
  rw [hp0,hp1,hout]
  have hm := hb 338
  have hf := hb (fillInput isE)
  simp only [List.length_cons,List.length_nil,Nat.zero_add,one_mul] at h0 h4
  have hs : scratch.length = 5 := rfl
  rw [hs] at h2 h6
  omega

/-- Copying and zero insertion retain both controller masks and all other
caller data outside the selected output and the five reclaimed scratch ports. -/
theorem fill_resources {n : ℕ} (isE : Bool) (a : Data) (H : Finset (Fin n))
    (bits : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hf : a.stacks (fillInput isE) = (List.ofFn bits).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : Data), ticks ≤ 100*(B+n+1)+1 ∧
      Trace (compiled (fillCommand isE) 338 (fillOutput isE)) ticks
        (a.withPC (some (compiled (fillCommand isE) 338 (fillOutput isE)).entry)) (b.withPC none) ∧
      b.stacks (fillOutput isE) = List.ofFn (HighIncidenceProgram.freeFill H bits) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠fillOutput isE → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled (fillCommand isE) 338 (fillOutput isE)) prefixSteps
          (a.withPC (some (compiled (fillCommand isE) 338 (fillOutput isE)).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+100*(B+n+1)+1 := by
  obtain ⟨rf,he⟩ := fillCommand_eval isE a H bits hm hf
  have ht := fillCommand_cost isE a B n hb rf
    (List.ofFn (HighIncidenceProgram.freeFill H bits)) (by simp)
  refine ⟨_,fillResult isE a rf (List.ofFn (HighIncidenceProgram.freeFill H bits)),
    Nat.add_le_add_right ht 1,compiled_halt_trace he 338 (fillOutput isE),?_,?_,?_,?_⟩
  · simp [fillResult_stack]
  · intro i hi
    have ho : i≠fillOutput isE := by
      intro h
      subst i
      cases isE <;> norm_num [fillOutput,scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi
    simp [fillResult_stack,ho,hi]
  · intro i hi ho
    simp [fillResult_stack,hi,ho]
  · have hmass : dataBits
        (a.withPC (some (compiled (fillCommand isE) 338 (fillOutput isE)).entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled (fillCommand isE) 338 (fillOutput isE))
      hmass prefixSteps intermediate (hp.trans (Nat.add_le_add_right ht 1)) htrace i
    omega



def expandCommand : Command := .seq (fillCommand true) (fillCommand false)

noncomputable def expandResult (a : Data) (rfE rfU : Fin 4 → Bool)
    (Eword Uword : List Bool) : Data :=
  fillResult false (fillResult true a rfE Eword) rfU Uword

theorem expandResult_stack (a : Data) (rfE rfU : Fin 4 → Bool)
    (Eword Uword : List Bool) (i : Fin 896) :
    (expandResult a rfE rfU Eword Uword).stacks i =
      if i=857 then Uword else if i=858 then Eword
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [expandResult,fillResult_stack,fillOutput,Bool.false_eq_true,↓reduceIte]
  by_cases hu : i=857
  · simp [hu]
  · by_cases he : i=858
    · subst i; simp [scratch]
    · by_cases hs : i ∈ scratch <;> simp [hu,he,hs]

theorem expandCommand_eval {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ ticks rfE rfU, ticks ≤ 300*(B+n+1) ∧ Eval expandCommand ticks a
      (expandResult a rfE rfU (List.ofFn (HighIncidenceProgram.freeFill H E))
        (List.ofFn (HighIncidenceProgram.freeFill H U))) := by
  obtain ⟨rfE,hE⟩ := fillCommand_eval true a H E hm he
  let b := fillResult true a rfE (List.ofFn (HighIncidenceProgram.freeFill H E))
  have hbm : b.stacks 338 = HighIncidenceProgram.descendingHighMask H := by
    simpa [b,fillResult_stack,fillOutput,scratch] using hm
  have hbu : b.stacks 835 = (List.ofFn U).reverse := by
    simpa [b,fillResult_stack,fillOutput,scratch] using hu
  have hbb : ∀ i, (b.stacks i).length ≤ B+n := by
    intro i
    rw [show b=fillResult true a rfE (List.ofFn (HighIncidenceProgram.freeFill H E)) from rfl,
      fillResult_stack]
    split_ifs
    · simp only [List.length_ofFn]
      exact Nat.le_add_left n B
    · exact Nat.zero_le _
    · exact (hb i).trans (Nat.le_add_right B n)
  obtain ⟨rfU,hU⟩ := fillCommand_eval false b H U hbm hbu
  have htE := fillCommand_cost true a B n hb rfE
    (List.ofFn (HighIncidenceProgram.freeFill H E)) (by simp)
  have htU := fillCommand_cost false b (B+n) n hbb rfU
    (List.ofFn (HighIncidenceProgram.freeFill H U)) (by simp)
  exact ⟨_,rfE,rfU,by omega,hE.seq hU⟩

/-- One concrete run expands both reversed residual masks to full ambient
masks and returns every allocated scratch stack empty. -/
theorem expand_resources {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : Data), ticks ≤ 300*(B+n+1)+1 ∧
      Trace (compiled expandCommand 338 857) ticks
        (a.withPC (some (compiled expandCommand 338 857).entry)) (b.withPC none) ∧
      b.stacks 858 = List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857 = List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠857 → i≠858 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled expandCommand 338 857) prefixSteps
          (a.withPC (some (compiled expandCommand 338 857).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+300*(B+n+1)+1 := by
  obtain ⟨ticks,rfE,rfU,ht,htrace⟩ := expandCommand_eval a H E U B hm he hu hb
  refine ⟨ticks+1,_,by omega,compiled_halt_trace htrace 338 857,?_,?_,?_,?_,?_⟩
  · simp [expandResult_stack]
  · simp [expandResult_stack]
  · intro i hi
    have h857 : i≠857 := by intro h; subst i; norm_num [scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi
    have h858 : i≠858 := by intro h; subst i; norm_num [scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi
    simp [expandResult_stack,h857,h858,hi]
  · intro i hi h857 h858
    simp [expandResult_stack,hi,h857,h858]
  · have hmass : dataBits (a.withPC (some (compiled expandCommand 338 857).entry)) ≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled expandCommand 338 857)
      hmass prefixSteps intermediate (hp.trans (show ticks+1≤300*(B+n+1)+1 by omega)) htrace i
    omega



abbrev CallerData := State 40 896

def callerRegister (i : Fin 16) : Fin 40 := i.castLE (by decide)
def setupCaller : Cmd 40 896 := liftCommand setupCommand 338 832 callerRegister id
def expandCaller : Cmd 40 896 := liftCommand expandCommand 338 857 callerRegister id

theorem callerRegister_injective : Function.Injective callerRegister := Fin.castLE_injective (by decide)

/-- The real shared-ABI setup call, ready for structured-command sequencing.
The boundary word bound is preserved even though all internal prefixes are charged. -/
theorem setupCaller_eval {n : ℕ} (a : CallerData) (H : Finset (Fin n)) (J B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hj : a.stacks 243 = List.replicate J true)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 120*(B+1)+1 ∧ Eval setupCaller ticks a b ∧
      b.stacks 832 = List.replicate (n-H.card) true ∧
      b.stacks 833 = List.replicate J true ∧ b.stacks 834 = [] ∧ b.stacks 835 = [] ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠832 → i≠833 → i≠834 → i≠835 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨ticks,b,ht,htrace,h832,h833,h834,h835,hs,hframe,_⟩ :=
    setup_resources (projectState callerRegister id a) H J B hm hj hb
  have he := eval_call_from_state (compiled setupCommand 338 832) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks,out,ht,he,(hout 832).trans h832,(hout 833).trans h833,
    (hout 834).trans h834,(hout 835).trans h835,
    fun i hi => (hout i).trans (hs i hi),
    fun i hi h832 h833 h834 h835 => (hout i).trans (hframe i hi h832 h833 h834 h835),?_⟩
  have hn : n≤B := by
    have h:=hb 338
    simpa [hm,HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using h
  have hJ : J≤B := by simpa [hj] using hb 243
  intro i
  rw [hout]
  by_cases h832' : i=832
  · subst i; rw [h832,List.length_replicate]; exact (Nat.sub_le _ _).trans hn
  · by_cases h833' : i=833
    · subst i; simpa [h833] using hJ
    · by_cases h834' : i=834
      · subst i; simp [h834]
      · by_cases h835' : i=835
        · subst i; simp [h835]
        · by_cases hi : i∈scratch
          · simp [hs i hi]
          · rw [hframe i hi h832' h833' h834' h835']
            exact hb i

/-- The actual shared-ABI mask expansion is directly composable and restores
the same boundary word bound, since the retained high mask already has length n. -/
theorem expandCaller_eval {n : ℕ} (a : CallerData) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 300*(B+n+1)+1 ∧ Eval expandCaller ticks a b ∧
      b.stacks 858 = List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857 = List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠857 → i≠858 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨ticks,b,ht,htrace,hE,hU,hs,hframe,_⟩ :=
    expand_resources (projectState callerRegister id a) H E U B hm he hu hb
  have hcall := eval_call_from_state (compiled expandCommand 338 857) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks,out,ht,hcall,(hout 858).trans hE,(hout 857).trans hU,
    fun i hi => (hout i).trans (hs i hi),
    fun i hi h857 h858 => (hout i).trans (hframe i hi h857 h858),?_⟩
  have hn : n≤B := by
    have h:=hb 338
    simpa [hm,HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using h
  intro i
  rw [hout]
  by_cases h857 : i=857
  · subst i; simpa [hU] using hn
  · by_cases h858 : i=858
    · subst i; simpa [hE] using hn
    · by_cases hi : i∈scratch
      · simp [hs i hi]
      · rw [hframe i hi h857 h858]
        exact hb i

/-- The fixed shared forty-register leaf ABI invokes the same concrete setup.
The call return and the caller halt are included in the time and prefix bound. -/
theorem setupCaller_resources {n : ℕ} (a : CallerData) (H : Finset (Fin n)) (J B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hj : a.stacks 243 = List.replicate J true)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 120*(B+1)+2 ∧
      Trace (compiled setupCaller 338 832) ticks
        (a.withPC (some (compiled setupCaller 338 832).entry)) (b.withPC none) ∧
      b.stacks 832 = List.replicate (n-H.card) true ∧
      b.stacks 833 = List.replicate J true ∧ b.stacks 834 = [] ∧ b.stacks 835 = [] ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠832 → i≠833 → i≠834 → i≠835 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled setupCaller 338 832) prefixSteps
          (a.withPC (some (compiled setupCaller 338 832).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+120*(B+1)+2 := by
  obtain ⟨ticks,b,ht,htrace,h832,h833,h834,h835,hs,hframe,_⟩ :=
    setup_resources (projectState callerRegister id a) H J B hm hj hb
  have he := eval_call_from_state (compiled setupCommand 338 832) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks+1,out,by omega,compiled_halt_trace he 338 832,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hout 832).trans h832
  · exact (hout 833).trans h833
  · exact (hout 834).trans h834
  · exact (hout 835).trans h835
  · intro i hi
    exact (hout i).trans (hs i hi)
  · intro i hi h832 h833 h834 h835
    exact (hout i).trans (hframe i hi h832 h833 h834 h835)
  · have hmass : dataBits (a.withPC (some (compiled setupCaller 338 832).entry)) ≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled setupCaller 338 832)
      hmass prefixSteps intermediate (hp.trans (show ticks+1≤120*(B+1)+2 by omega)) htrace i
    omega

/-- Ambient E/U words and controller preservation in the shared leaf ABI.
No callback, decoder oracle or supplied successful layout is assumed. -/
theorem expandCaller_resources {n : ℕ} (a : CallerData) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 300*(B+n+1)+2 ∧
      Trace (compiled expandCaller 338 857) ticks
        (a.withPC (some (compiled expandCaller 338 857).entry)) (b.withPC none) ∧
      b.stacks 858 = List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857 = List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠857 → i≠858 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled expandCaller 338 857) prefixSteps
          (a.withPC (some (compiled expandCaller 338 857).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+300*(B+n+1)+2 := by
  obtain ⟨ticks,b,ht,htrace,hE,hU,hs,hframe,_⟩ :=
    expand_resources (projectState callerRegister id a) H E U B hm he hu hb
  have hcall := eval_call_from_state (compiled expandCommand 338 857) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks+1,out,by omega,compiled_halt_trace hcall 338 857,?_,?_,?_,?_,?_⟩
  · exact (hout 858).trans hE
  · exact (hout 857).trans hU
  · intro i hi
    exact (hout i).trans (hs i hi)
  · intro i hi h857 h858
    exact (hout i).trans (hframe i hi h857 h858)
  · have hmass : dataBits (a.withPC (some (compiled expandCaller 338 857).entry)) ≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled expandCaller 338 857)
      hmass prefixSteps intermediate (hp.trans (show ticks+1≤300*(B+n+1)+2 by omega)) htrace i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
