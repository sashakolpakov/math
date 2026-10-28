import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyCorrectness

namespace OAI.Algorithms

/-!
# Exact accounting for the prepared-block controller

The functions below count the concrete parser, writer, transfer, counter,
and table-source calls. The execution theorem is developed against these
counts; merely defining a count is not an execution bound.
-/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

def factorSteps (zero one : Word) (rows : List SubexpTableSource.Row) : ℕ :=
  9 * (SubexpTableSource.encodeRows rows).length +
    SubexpTableSource.tableCost zero one rows +
    6 * (SubexpTableSource.tableCode zero one rows).length + 21

def factorProductSteps (zero one : Word) (fs : List (List SubexpTableSource.Row)) : ℕ :=
  (fs.map (factorSteps zero one)).sum + 6 * fs.length + 8 * one.length +
    3 * (factorProduct zero one fs).length + 17

def termSteps (zero one : Word) (t : Term) : ℕ :=
  factorProductSteps zero one t.factors + 19 * t.weight.length +
    10 * (factorProduct zero one t.factors).length +
    13 * (SubexpKernelControl.encodeTerm (compiledTerm zero one t)).length + 48

def groupSteps (zero one : Word) (ts : List Term) : ℕ :=
  (ts.map (fun t => 9 * (encodeTerm t).length + termSteps zero one t + 9)).sum +
    13 * (SubexpKernelControl.encodeGroup (ts.map (compiledTerm zero one))).length + 19

def blockSteps (zero one : Word) (b : Block) : ℕ :=
  (b.groups.map (fun ts => 9 * (encodeGroup ts).length + groupSteps zero one ts + 9)).sum +
    19 * b.outside.length +
    13 * (Encoding.encodeList SubexpKernelControl.encodeGroup
      (b.groups.map (fun ts => ts.map (compiledTerm zero one)))).length +
    13 * (SubexpKernelControl.encodeBlock (compiledBlock zero one b)).length + 55

def assemblySteps (zero one : Word) (bs : List Block) : ℕ :=
  (bs.map (fun b => 9 * (encodeBlock b).length + blockSteps zero one b + 9)).sum +
    3 * (assembled zero one bs).length + 11

/-- Measured and unmeasured executions of the same finite command have the
same final state. This reuses checked state transformations when adding counts. -/
theorem measured_result {cmd : Code} {n : ℕ} {a b c : Data}
    (h : Eval cmd n a b) (hc : Executes cmd a c) : Eval cmd n a c := by
  obtain ⟨m,hm⟩ := hc
  have h1 := StructuredCalls.compiled_halt_trace h 0 0
  have h2 := StructuredCalls.compiled_halt_trace hm 0 0
  have he := Computation.RunsIn.terminal_unique
    (show BitProgram.RunsIn (StructuredCalls.compiled cmd 0 0) (n+1) _ _ from ⟨_,le_rfl,h1⟩)
    (show BitProgram.RunsIn (StructuredCalls.compiled cmd 0 0) (m+1) _ _ from ⟨_,le_rfl,h2⟩)
    (by simp [BitProgram.step,StructuredProgram.State.withPC])
    (by simp [BitProgram.step,StructuredProgram.State.withPC])
  have hbc : b=c := congrArg StructuredProgram.State.ofCfg he
  simpa only [hbc] using h

private def parserData' (v p : Bool) (input scratch : Word) : State 2 2 :=
  ⟨ParserProgram.pair v p,ParserProgram.pair input scratch⟩

theorem frame_measured (d : Data) (bits rest : Word)
    (h0 : d.stacks 0 = Encoding.frame bits ++ rest) (h4 : d.stacks 4 = []) :
    Eval (.call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs (pairPorts 0 4)))
      (6*bits.length+4) d (parserState d false true rest bits.reverse) := by
  have ht := ParserProgram.frame_trace bits rest [] (d.regs 0) (d.regs 1)
  simp only [List.append_nil] at ht
  have h := eval_call_lifted ParserProgram.frameProgram parserRegs (pairPorts 0 4) d
    (by decide) (by decide)
    (a := parserData' (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) [])
    (b := parserData' false true rest bits.reverse) ht
  have ha : embedState parserRegs (pairPorts 0 4) d
      (parserData' (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) []) = d := by
    have he := embed_parser d (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) []
    rw [←h0,←h4,parserState_self] at he
    rw [←h0,←h4]
    exact he
  rw [ha] at h
  exact measured_result h (frame_exec d bits rest h0 h4)

theorem unframe_measured (v p c : Bool) (bits rest zero one : Word) (a : Buffers) :
    Eval unframe (9*bits.length+7)
      (state v p c (Encoding.frame bits ++ rest) zero one a)
      (state false false c (bits ++ rest) zero one a) := by
  let d := state v p c (Encoding.frame bits ++ rest) zero one a
  have h := eval_call_lifted ParserProgram.unframeProgram parserRegs (pairPorts 0 4) d
    (by decide) (by decide)
    (a := parserData' v p (Encoding.frame bits ++ rest) [])
    (b := parserData' false false (bits ++ rest) []) (ParserProgram.unframe_trace bits rest v p)
  have ha : embedState parserRegs (pairPorts 0 4) d
      (parserData' v p (Encoding.frame bits ++ rest) []) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ (by decide) (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i
      · exact (hi ⟨0,rfl⟩).elim
      · exact (hi ⟨1,rfl⟩).elim
      · rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  rw [ha] at h
  exact measured_result h (unframe_work v p c bits rest zero one a)

theorem capture_measured (v p c : Bool) (bits rest zero one : Word) (a : Buffers) :
    Eval capture (9*bits.length+7)
      (state v p c (Encoding.frame bits ++ rest) zero one a)
      (work false false c rest zero one a bits []) := by
  let d := state v p c (Encoding.frame bits ++ rest) zero one a
  have h1 := frame_measured d bits rest rfl rfl
  have h2 := transfer_eval 4 19 (by decide) (parserState d false true rest bits.reverse)
  have h := measured_result (Eval.seq h1 h2) (capture_work v p c bits rest zero one a)
  have hlen : ((parserState d false true rest bits.reverse).stacks 4).length = bits.length := by
    simp [parserState]
  rw [hlen] at h
  have hcost : 6 * bits.length + 4 + (3 * bits.length + 3) = 9 * bits.length + 7 := by
    omega
  rw [hcost] at h
  exact h

theorem appendRecord_measured (i : Fin 7) (v p c : Bool) (input zero one payload : Word)
    (a : Buffers) :
    Eval (appendRecord 19 (bufferPort i)) (8*payload.length+9)
      (work v p c input zero one a payload [])
      (work false false true input zero one (emit i (record payload) a) payload []) :=
  measured_result
    (appendRecord_eval 19 (bufferPort i) (by fin_cases i <;> decide) (by decide)
      (by fin_cases i <;> decide) (work v p c input zero one a payload []) rfl)
    (appendRecord_work i v p c input zero one payload a)

theorem clearPayload_measured (v p c : Bool) (input zero one payload : Word) (a : Buffers) :
    Eval (clear 19) (2*payload.length+3) (work v p c input zero one a payload [])
      (state false false c input zero one a) :=
  measured_result (clear_eval 19 (work v p c input zero one a payload []))
    (clearPayload_work v p c input zero one payload a)

theorem appendCapturedRecord_measured (i : Fin 7) (v p c : Bool)
    (bits rest zero one : Word) (a : Buffers) :
    Eval (appendCapturedRecord (bufferPort i)) (19*bits.length+19)
      (state v p c (Encoding.frame bits ++ rest) zero one a)
      (state false false true rest zero one (emit i (record bits) a)) := by
  have h := Eval.seq (capture_measured v p c bits rest zero one a)
    (Eval.seq (appendRecord_measured i false false c rest zero one bits a)
      (clearPayload_measured false false true rest zero one bits (emit i (record bits) a)))
  have hcost : 9 * bits.length + 7 + ((8 * bits.length + 9) +
      (2 * bits.length + 3)) = 19 * bits.length + 19 := by
    omega
  rw [hcost] at h
  exact h

theorem pushBuffer_measured (i : Fin 7) (bit v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Eval (pushBit (bufferPort i) bit) 2 (state v p c input zero one a)
      (state bit p c input zero one (Function.update a i (bit::a i))) :=
  measured_result (pushBit_eval (bufferPort i) bit (state v p c input zero one a))
    (pushBuffer_work i bit v p c input zero one a)

theorem transferBuffer_measured (i : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Eval (transfer (bufferPort i) 19) (3*(a i).length+3) (state v p c input zero one a)
      (work false false c input zero one (Function.update a i []) (a i).reverse []) := by
  have h := measured_result
    (transfer_eval (bufferPort i) 19 (by fin_cases i <;> decide) (state v p c input zero one a))
    (transferBuffer_work i v p c input zero one a)
  have hp : (state v p c input zero one a).stacks (bufferPort i) = a i := by
    fin_cases i <;> rfl
  simpa only [hp] using h

theorem transferPayload_measured (i : Fin 7) (v p c : Bool)
    (input zero one payload : Word) (a : Buffers) :
    Eval (transfer 19 (bufferPort i)) (3*payload.length+3)
      (work v p c input zero one a payload [])
      (state false false c input zero one (emit i payload a)) :=
  measured_result
    (transfer_eval 19 (bufferPort i) (by fin_cases i <;> decide)
      (work v p c input zero one a payload []))
    (transferPayload_work i v p c input zero one payload a)

theorem reset_measured (v p c : Bool) (input zero one payload : Word) (a : Buffers) :
    Eval reset 3 (work v p c input zero one a payload [])
      (work false false false input zero one a payload []) :=
  measured_result (reset_eval (work v p c input zero one a payload []))
    (reset_work v p c input zero one payload a)

theorem closeInto_measured (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Eval (closeInto (bufferPort i) (bufferPort j)) (13*(a i).length+30)
      (state v p c input zero one a)
      (state false false true input zero one (closeUpdate i j a)) := by
  let b := Function.update a i (false::a i)
  have h1 := pushBuffer_measured i false v p c input zero one a
  have h2 := transferBuffer_measured i false p c input zero one b
  have h3 := appendRecord_measured j false false c input zero one (b i).reverse
    (Function.update b i [])
  have h4 := clearPayload_measured false false true input zero one (b i).reverse
    (emit j (record (b i).reverse) (Function.update b i []))
  have h := measured_result (Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)))
    (closeInto_work i j v p c input zero one a)
  have hlen : (b i).length = (a i).length + 1 := by
    simp [b]
  rw [List.length_reverse, hlen] at h
  have hcost : 2 + ((3 * ((a i).length + 1) + 3) +
      ((8 * ((a i).length + 1) + 9) + (2 * ((a i).length + 1) + 3))) =
      13 * (a i).length + 30 := by
    omega
  rw [hcost] at h
  exact h

theorem popTag_measured (b v p c : Bool) (rest zero one : Word) (a : Buffers) :
    Eval popTag 1 (state v p c (b::rest) zero one a) (state b true c rest zero one a) :=
  measured_result
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 1)
      (state v p c (b::rest) zero one a)))
    (popTag_work b v p c rest zero one a)

theorem popList_measured {α : Type*} (encode : α → Word) (xs : List α) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) :
    Eval popTag 1 (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (afterTag encode xs rest zero one c a) := by
  cases xs with
  | nil => simpa [afterTag,Encoding.encodeList] using popTag_measured false v p c rest zero one a
  | cons x xs =>
      simpa [afterTag,Encoding.encodeList,List.append_assoc] using popTag_measured true v p c
        (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

theorem scan_measured {α : Type*} (body : Code) (encode : α → Word) (cost : α → ℕ)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop)
    (zero one : Word) (vb pb cb : Bool)
    (hbody : ∀ x rest c a, inv a → Eval body (cost x)
      (state false false c (encode x ++ rest) zero one a)
      (state vb pb cb rest zero one (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (v p c : Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ c', Eval (scan body)
      (2 + (xs.map (fun x => 9*(encode x).length + cost x + 9)).sum)
      (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have loop : ∀ (xs : List α) c a, inv a → ∃ c',
      Eval (.while 0 (.seq unframe (.seq body popTag)))
        (1 + (xs.map (fun x => 9*(encode x).length + cost x + 9)).sum)
        (afterTag encode xs rest zero one c a)
        (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
    intro xs
    induction xs with
    | nil => intro c a ha; exact ⟨c,Eval.while_false rfl⟩
    | cons x xs ih =>
        intro c a ha
        let tail := Encoding.encodeList encode xs ++ rest
        have h1 := unframe_measured true true c (encode x) tail zero one a
        have h2 := hbody x tail c a ha
        have h3 := popList_measured encode xs vb pb cb rest zero one (update x a)
        obtain ⟨c',h4⟩ := ih cb (update x a) (hpreserve x a ha)
        refine ⟨c',?_⟩
        have h := Eval.while_true (by rfl :
          (afterTag encode (x::xs) rest zero one c a).regs 0 = true)
          (Eval.seq h1 (Eval.seq h2 h3)) h4
        have hcost :
            ((9 * (encode x).length + 7) + (cost x + 1)) +
                (1 + (xs.map (fun x => 9 * (encode x).length + cost x + 9)).sum) + 1 =
              1 + (((x :: xs).map (fun x =>
                9 * (encode x).length + cost x + 9)).sum) := by
          simp only [List.map_cons, List.sum_cons]
          omega
        rw [hcost] at h
        exact h
  obtain ⟨c',h⟩ := loop xs c a ha
  refine ⟨c',?_⟩
  have he := Eval.seq (popList_measured encode xs v p c rest zero one a) h
  have hcost : 1 + (1 + (xs.map (fun x => 9 * (encode x).length + cost x + 9)).sum) =
      2 + (xs.map (fun x => 9 * (encode x).length + cost x + 9)).sum := by
    omega
  rw [hcost] at he
  simpa only [scan] using he

theorem scanFrames_measured {α : Type*} (body : Code) (encode : α → Word) (cost : α → ℕ)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop)
    (zero one : Word) (vb pb cb : Bool)
    (hbody : ∀ x rest c a, inv a → Eval body (cost x)
      (state true true c (Encoding.frame (encode x) ++ rest) zero one a)
      (state vb pb cb rest zero one (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (v p c : Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ c', Eval (.seq popTag (.while 0 (.seq body popTag)))
      (2 + (xs.map (fun x => cost x + 2)).sum)
      (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have loop : ∀ (xs : List α) c a, inv a → ∃ c',
      Eval (.while 0 (.seq body popTag)) (1 + (xs.map (fun x => cost x+2)).sum)
        (afterTag encode xs rest zero one c a)
        (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
    intro xs
    induction xs with
    | nil => intro c a ha; exact ⟨c,Eval.while_false rfl⟩
    | cons x xs ih =>
        intro c a ha
        let tail := Encoding.encodeList encode xs ++ rest
        have h1 := hbody x tail c a ha
        have h2 := popList_measured encode xs vb pb cb rest zero one (update x a)
        obtain ⟨c',h3⟩ := ih cb (update x a) (hpreserve x a ha)
        refine ⟨c',?_⟩
        have h := Eval.while_true (by rfl :
          (afterTag encode (x::xs) rest zero one c a).regs 0 = true)
          (Eval.seq h1 h2) h3
        have hcost : (cost x + 1) +
            (1 + (xs.map (fun x => cost x + 2)).sum) + 1 =
            1 + (((x :: xs).map (fun x => cost x + 2)).sum) := by
          simp only [List.map_cons, List.sum_cons]
          omega
        rw [hcost] at h
        exact h
  obtain ⟨c',h⟩ := loop xs c a ha
  refine ⟨c',?_⟩
  have he := Eval.seq (popList_measured encode xs v p c rest zero one a) h
  have hcost : 1 + (1 + (xs.map (fun x => cost x + 2)).sum) =
      2 + (xs.map (fun x => cost x + 2)).sum := by
    omega
  rw [hcost] at he
  exact he

theorem factorBody_measured (rows : List SubexpTableSource.Row) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) :
    Eval (factorBody SubexpTableSource.program) (factorSteps zero one rows)
      (state v p c (Encoding.frame (SubexpTableSource.encodeRows rows) ++ rest) zero one a)
      (state true false false rest zero one (factorUpdate zero one rows a)) := by
  have h1 := capture_measured v p c (SubexpTableSource.encodeRows rows) rest zero one a
  have h2 := reset_measured false false c rest zero one (SubexpTableSource.encodeRows rows) a
  have h3 := table_work_eval rows rest zero one a
  have h4 := transferPayload_measured 0 false false false rest zero one
    (SubexpTableSource.tableCode zero one rows) a
  have h5 := pushBuffer_measured 1 true false false false rest zero one
    (emit 0 (SubexpTableSource.tableCode zero one rows) a)
  have h := measured_result (Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 h5))))
    (factorBody_work rows v p c rest zero one a)
  have hcost :
      (9 * (SubexpTableSource.encodeRows rows).length + 7) +
        (3 + ((SubexpTableSource.tableCost zero one rows +
          3 * (SubexpTableSource.tableCode zero one rows).length + 6) +
          ((3 * (SubexpTableSource.tableCode zero one rows).length + 3) + 2))) =
        factorSteps zero one rows := by
    dsimp [factorSteps]
    omega
  rw [hcost] at h
  exact h

theorem sum_add_constant {α : Type*} (f : α → ℕ) (xs : List α) (k : ℕ) :
    (xs.map (fun x => f x+k)).sum = (xs.map f).sum + k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]; omega

theorem factors_measured (fs : List (List SubexpTableSource.Row)) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) (h0 : a 0 = []) (h1 : a 1 = []) :
    Eval factorCommand (factorProductSteps zero one fs)
      (state v p c (Encoding.encodeList SubexpTableSource.encodeRows fs ++ rest) zero one a)
      (work false false true rest zero one a (factorProduct zero one fs) []) := by
  let pending := fs.foldl (fun a rows => factorUpdate zero one rows a) a
  obtain ⟨c',hs⟩ := scanFrames_measured (factorBody SubexpTableSource.program)
    SubexpTableSource.encodeRows (factorSteps zero one) (factorUpdate zero one) (fun _ => True)
    zero one true false false
    (fun rows rest c a _ => factorBody_measured rows true true c rest zero one a)
    (fun _ _ _ => trivial) fs v p c rest a trivial
  have ho := appendOne_work_eval false true c' rest zero one pending
  have hd := drainProducts_work_eval false false rest zero one
    (emit 0 (SubexpKernelControl.pushWord one) pending)
  let ready := drainUpdate (emit 0 (SubexpKernelControl.pushWord one) pending)
  have ht := transferBuffer_measured 0 false false true rest zero one ready
  have hc : (emit 0 (SubexpKernelControl.pushWord one) pending) 1 =
      List.replicate fs.length true := by
    dsimp [pending]
    rw [factorFold]
    simp [emit,h1]
  have hcode : (ready 0).reverse = factorProduct zero one fs := by
    dsimp [ready,pending]
    rw [factorFold]
    simp [drainUpdate,emit,factorProduct,h0,h1,List.reverse_append,List.append_assoc]
  have hlen : (ready 0).length = (factorProduct zero one fs).length := by
    simpa only [List.length_reverse] using congrArg List.length hcode
  have h := measured_result (Eval.seq hs (Eval.seq ho (Eval.seq hd ht)))
    (factors_work fs v p c rest zero one a h0 h1)
  rw [hc,List.length_replicate,hlen,sum_add_constant] at h
  have hcost :
      (2 + ((fs.map (factorSteps zero one)).sum + 2 * fs.length)) +
        ((8 * one.length + 9) +
          ((4 * fs.length + 3) +
            (3 * (factorProduct zero one fs).length + 3))) =
        factorProductSteps zero one fs := by
    dsimp [factorProductSteps]
    omega
  rw [hcost] at h
  exact h

theorem termBody_measured (t : Term) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) :
    Eval (termBody SubexpTableSource.program) (termSteps zero one t)
      (state false false c (encodeTerm t ++ rest) zero one a)
      (state false false true rest zero one (termUpdate zero one t a)) := by
  let weighted := emit 2 (record t.weight) a
  have hw := appendCapturedRecord_measured 2 false false c t.weight
    (Encoding.encodeList SubexpTableSource.encodeRows t.factors ++ rest) zero one a
  have hf := factors_measured t.factors false false true rest zero one weighted
    (by simpa [weighted,emit] using h0) (by simpa [weighted,emit] using h1)
  have hr := appendRecord_measured 2 false false true rest zero one
    (factorProduct zero one t.factors) weighted
  let both := emit 2 (record (factorProduct zero one t.factors)) weighted
  have hc := clearPayload_measured false false true rest zero one
    (factorProduct zero one t.factors) both
  have he := closeInto_measured 2 3 false false true rest zero one both
  have h := measured_result (Eval.seq hw (Eval.seq hf (Eval.seq hr (Eval.seq hc he))))
    (by simpa only [termBody, factorCommand, bufferPort_two, bufferPort_three, encodeTerm,
        List.append_assoc] using
      termBody_work t c rest zero one a h0 h1 h2)
  have hl : (both 2).length + 1 =
      (SubexpKernelControl.encodeTerm (compiledTerm zero one t)).length := by
    simp [both,weighted,emit,h2,SubexpKernelControl.encodeTerm,compiledTerm,
      Encoding.encodeList,record,List.length_append]
    omega
  have hcost :
      (19 * t.weight.length + 19) +
        (factorProductSteps zero one t.factors +
          ((8 * (factorProduct zero one t.factors).length + 9) +
            ((2 * (factorProduct zero one t.factors).length + 3) +
              (13 * (both 2).length + 30)))) = termSteps zero one t := by
    dsimp [termSteps]
    omega
  rw [hcost] at h
  simpa only [termBody, factorCommand, bufferPort_two, bufferPort_three, encodeTerm,
    List.append_assoc] using h

theorem groupBody_measured (ts : List Term) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) (h3 : a 3 = []) :
    Eval (groupBody SubexpTableSource.program) (groupSteps zero one ts)
      (state false false c (encodeGroup ts ++ rest) zero one a)
      (state false false true rest zero one (groupUpdate zero one ts a)) := by
  let inv : Buffers → Prop := fun a => a 0=[] ∧ a 1=[] ∧ a 2=[]
  obtain ⟨c',hs⟩ := scan_measured (termBody SubexpTableSource.program) encodeTerm
    (termSteps zero one) (termUpdate zero one) inv zero one false false true
    (fun t rest c a h => termBody_measured t c rest zero one a h.1 h.2.1 h.2.2)
    (by intro t a h; simpa [inv,termUpdate,emit] using h)
    ts false false c rest a ⟨h0,h1,h2⟩
  let pending := ts.foldl (fun a t => termUpdate zero one t a) a
  have hc := closeInto_measured 3 6 false true c' rest zero one pending
  have hl : (pending 3).length+1 =
      (SubexpKernelControl.encodeGroup (ts.map (compiledTerm zero one))).length := by
    dsimp [pending,termUpdate]
    rw [fold_emit]
    simp [emit,h3,SubexpKernelControl.encodeGroup,encodeList_eq_records,
      List.map_map,Function.comp_def]
  have h := measured_result (Eval.seq hs hc) (groupBody_work ts c rest zero one a h0 h1 h2 h3)
  have hcost :
      (2 + (ts.map (fun t => 9 * (encodeTerm t).length + termSteps zero one t + 9)).sum) +
        (13 * (pending 3).length + 30) = groupSteps zero one ts := by
    dsimp [groupSteps]
    omega
  rw [hcost] at h
  exact h

theorem blockBody_measured (b : Block) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) (h3 : a 3 = [])
    (h4 : a 4 = []) (h6 : a 6 = []) :
    Eval (blockBody SubexpTableSource.program) (blockSteps zero one b)
      (state false false c (encodeBlock b ++ rest) zero one a)
      (state false false true rest zero one (blockUpdate zero one b a)) := by
  let outside := emit 4 (record b.outside) a
  have ho := appendCapturedRecord_measured 4 false false c b.outside
    (Encoding.encodeList encodeGroup b.groups ++ rest) zero one a
  let inv : Buffers → Prop := fun a => a 0=[] ∧ a 1=[] ∧ a 2=[] ∧ a 3=[]
  obtain ⟨c',hs⟩ := scan_measured (groupBody SubexpTableSource.program) encodeGroup
    (groupSteps zero one) (groupUpdate zero one) inv zero one false false true
    (fun ts rest c a h => groupBody_measured ts c rest zero one a h.1 h.2.1 h.2.2.1 h.2.2.2)
    (by intro ts a h; simpa [inv,groupUpdate,emit] using h)
    b.groups false false true rest outside
    (by simpa [inv,outside,emit] using And.intro h0 (And.intro h1 (And.intro h2 h3)))
  let pending := b.groups.foldl (fun a ts => groupUpdate zero one ts a) outside
  have hg := closeInto_measured 6 4 false true c' rest zero one pending
  have hb := closeInto_measured 4 5 false false true rest zero one (closeUpdate 6 4 pending)
  have hglen : (pending 6).length+1 =
      (Encoding.encodeList SubexpKernelControl.encodeGroup
        (b.groups.map (fun ts => ts.map (compiledTerm zero one)))).length := by
    dsimp [pending,groupUpdate]
    rw [fold_emit]
    simp [emit,outside,h6,encodeList_eq_records,List.map_map,Function.comp_def]
  have hblen : ((closeUpdate 6 4 pending) 4).length+1 =
      (SubexpKernelControl.encodeBlock (compiledBlock zero one b)).length := by
    dsimp [pending,groupUpdate]
    rw [fold_emit,close_emitted 6 4 _ outside (by simpa [outside,emit] using h6)]
    simp [outside,emit,h4,compiledBlock,SubexpKernelControl.encodeBlock,
      encodeList_eq_records,record,List.map_map,Function.comp_def,List.length_append]
    omega
  have h := measured_result (Eval.seq ho (Eval.seq hs (Eval.seq hg hb)))
    (by simpa only [blockBody, bufferPort_four, bufferPort_five, bufferPort_six,
        encodeBlock, List.append_assoc] using
      blockBody_work b c rest zero one a h0 h1 h2 h3 h4 h6)
  have hcost :
      (19 * b.outside.length + 19) +
        ((2 + (b.groups.map (fun ts =>
          9 * (encodeGroup ts).length + groupSteps zero one ts + 9)).sum) +
          ((13 * (pending 6).length + 30) +
            (13 * ((closeUpdate 6 4 pending) 4).length + 30))) =
        blockSteps zero one b := by
    dsimp [blockSteps]
    omega
  rw [hcost] at h
  simpa only [blockBody, bufferPort_four, bufferPort_five, bufferPort_six,
    encodeBlock, List.append_assoc] using h

theorem actualProgram_measured (zero one : Word) (bs : List Block) :
    Trace actualProgram (assemblySteps zero one bs)
      ((serviceState (encodeBlocks bs) zero one).withPC (some actualProgram.entry))
      ((serviceState (assembled zero one bs) zero one).withPC none) := by
  let inv : Buffers → Prop := fun a => a 0=[] ∧ a 1=[] ∧ a 2=[] ∧ a 3=[] ∧ a 4=[] ∧ a 6=[]
  obtain ⟨c',hs⟩ := scan_measured (blockBody SubexpTableSource.program) encodeBlock
    (blockSteps zero one) (blockUpdate zero one) inv zero one false false true
    (fun b rest c a h => blockBody_measured b c rest zero one a h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (by intro b a h; simpa [inv,blockUpdate,emit] using h)
    bs false false false [] emptyBuffers (by simp [inv,emptyBuffers])
  let pending := bs.foldl (fun a b => blockUpdate zero one b a) emptyBuffers
  have hp := pushBuffer_measured 5 false false true c' [] zero one pending
  let ready := Function.update pending 5 (false::pending 5)
  have ht := measured_result (transfer_eval 18 0 (by decide) (state false true c' [] zero one ready))
    (transferOutput_work false true c' zero one ready)
  have hr := reset_measured false false c' (ready 5).reverse zero one [] (Function.update ready 5 [])
  have hraw := Eval.seq hs (Eval.seq hp (Eval.seq ht hr))
  simp only [List.append_nil] at hraw
  have h := measured_result hraw (actualCommand_exec zero one bs)
  have hlen : (ready 5).length = (assembled zero one bs).length := by
    dsimp [ready,pending,blockUpdate]
    rw [fold_emit]
    simp [emit,emptyBuffers,assembled,SubexpKernelControl.encodeBlocks,encodeList_eq_records,
      List.map_map,Function.comp_def]
  have hh := StructuredCalls.compiled_halt_trace h 0 0
  change Trace actualProgram
    ((2+(bs.map (fun b => 9*(encodeBlock b).length+blockSteps zero one b+9)).sum)+
      (2+((3*(ready 5).length+3)+3))+1) _ _ at hh
  rw [hlen] at hh
  have hcost :
      ((2 + (bs.map (fun b =>
        9 * (encodeBlock b).length + blockSteps zero one b + 9)).sum) +
        (2 + ((3 * (assembled zero one bs).length + 3) + 3)) + 1) =
        assemblySteps zero one bs := by
    dsimp [assemblySteps]
    omega
  rw [hcost] at hh
  exact hh

theorem actualProgram_runsIn (zero one : Word) (bs : List Block) :
    RunsIn actualProgram (assemblySteps zero one bs)
      ((serviceState (encodeBlocks bs) zero one).withPC (some actualProgram.entry))
      ((serviceState (assembled zero one bs) zero one).withPC none) :=
  ⟨_,le_rfl,actualProgram_measured zero one bs⟩

theorem primitive_execution (zero one : Word) (bs : List Block) :
    Computation.RunsIn (BitProgram.primitive actualProgram).step
      (BitProgram.primitiveOverhead actualProgram * assemblySteps zero one bs)
      (BitProgram.primitiveCfg actualProgram
        ((serviceState (encodeBlocks bs) zero one).withPC (some actualProgram.entry)))
      (BitProgram.primitiveCfg actualProgram
        ((serviceState (assembled zero one bs) zero one).withPC none)) :=
  BitProgram.primitive_execution actualProgram (actualProgram_runsIn zero one bs)

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
