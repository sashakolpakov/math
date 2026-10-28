import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyExecution

namespace OAI.Algorithms

/-! Framed input traversal for the prepared-block constructor. -/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

def parserState (frame : Data) (v p : Bool) (input scratch : Word) : Data :=
  ⟨SubexpHornerProgram.triple v p (frame.regs 2),
    Function.update (Function.update frame.stacks 0 input) 4 scratch⟩

private def parserData (v p : Bool) (input scratch : Word) : State 2 2 :=
  ⟨ParserProgram.pair v p, ParserProgram.pair input scratch⟩

theorem embed_parser (frame : Data) (v p : Bool) (input scratch : Word) :
    embedState parserRegs (pairPorts 0 4) frame (parserData v p input scratch) =
      parserState frame v p input scratch := by
  apply embedState_eq_of_ports _ _ _ _ _ (by decide) (by decide)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi ⟨0,rfl⟩).elim
    · exact (hi ⟨1,rfl⟩).elim
    · rfl
  · intro i; fin_cases i <;> simp [parserState,parserData,pairPorts,ParserProgram.pair]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [pairPorts] using h.symm⟩
    have h4 : i ≠ 4 := fun h => hi ⟨1,by simpa [pairPorts] using h.symm⟩
    simp [parserState,h0,h4]

theorem parserState_self (d : Data) :
    parserState d (d.regs 0) (d.regs 1) (d.stacks 0) (d.stacks 4) = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    by_cases h0 : i = 0 <;> by_cases h4 : i = 4 <;>
      simp_all

theorem unframe_exec (d : Data) (bits rest : Word)
    (h0 : d.stacks 0 = Encoding.frame bits ++ rest) (h4 : d.stacks 4 = []) :
    Executes unframe d (parserState d false false (bits ++ rest) []) := by
  have h := eval_call_lifted ParserProgram.unframeProgram parserRegs (pairPorts 0 4) d
    (by decide) (by decide)
    (a := parserData (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) [])
    (b := parserData false false (bits ++ rest) [])
    (ParserProgram.unframe_trace bits rest (d.regs 0) (d.regs 1))
  simp only [embed_parser] at h
  rw [←h0,←h4,parserState_self] at h
  simpa only [h4] using (show Executes unframe d _ from ⟨_,h⟩)

theorem frame_exec (d : Data) (bits rest : Word)
    (h0 : d.stacks 0 = Encoding.frame bits ++ rest) (h4 : d.stacks 4 = []) :
    Executes (.call (ProgramLinking.liftProgram ParserProgram.frameProgram
      parserRegs (pairPorts 0 4))) d (parserState d false true rest bits.reverse) := by
  have ht := ParserProgram.frame_trace bits rest [] (d.regs 0) (d.regs 1)
  simp only [List.append_nil] at ht
  have h := eval_call_lifted ParserProgram.frameProgram parserRegs (pairPorts 0 4) d
    (by decide) (by decide)
    (a := parserData (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) [])
    (b := parserData false true rest bits.reverse) ht
  simp only [embed_parser] at h
  rw [←h0,←h4,parserState_self] at h
  exact ⟨_,h⟩

def afterCapture (d : Data) (bits rest : Word) : Data :=
  ⟨SubexpHornerProgram.triple false false (d.regs 2),
    Function.update (Function.update d.stacks 0 rest) 19 bits⟩

theorem capture_exec (d : Data) (bits rest : Word)
    (h0 : d.stacks 0 = Encoding.frame bits ++ rest)
    (h4 : d.stacks 4 = []) (h19 : d.stacks 19 = []) :
    Executes capture d (afterCapture d bits rest) := by
  have h1 := frame_exec d bits rest h0 h4
  have h2 := transfer_exec 4 19 (by decide) (parserState d false true rest bits.reverse)
  have he : afterTransfer 4 19 (parserState d false true rest bits.reverse) =
      afterCapture d bits rest := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [parserState,readRegs,SubexpHornerProgram.triple]
    · funext i
      fin_cases i <;>
        simp [parserState,StackRoutines.transferStacks,h4,h19]
  rw [he] at h2
  exact executes_seq h1 h2

def popped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 0).head?, Function.update d.stacks 0 (d.stacks 0).tail⟩

theorem popTag_exec (d : Data) : Executes popTag d (popped d) :=
  ⟨1,Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 1) d)⟩

/-- The seven unbounded accumulators are product bytes, a unary factor count,
term bytes, group bytes, block bytes, outer bytes, and a block's group-list bytes. -/
abbrev Buffers := Fin 7 → Word

def work (v p c : Bool) (input zero one : Word) (a : Buffers)
    (payload scratch : Word) : Data :=
  ⟨SubexpHornerProgram.triple v p c,
    ![input,zero,one,[],scratch,[],[],[],[],[],[],[],[],
      a 0,a 1,a 2,a 3,a 4,a 5,payload,[],a 6]⟩

def state (v p c : Bool) (input zero one : Word) (a : Buffers) : Data :=
  work v p c input zero one a [] []

def bufferPort : Fin 7 → Fin 22 := ![13,14,15,16,17,18,21]

def emit (i : Fin 7) (bits : Word) (a : Buffers) : Buffers :=
  Function.update a i (bits.reverse ++ a i)

def emptyBuffers : Buffers := fun _ => []

theorem emit_emit (i : Fin 7) (x y : Word) (a : Buffers) :
    emit i y (emit i x a) = emit i (x ++ y) a := by
  funext j
  by_cases h : j=i
  · subst j; simp [emit,List.reverse_append,List.append_assoc]
  · simp [emit,h]

theorem capture_work (v p c : Bool) (bits rest zero one : Word) (a : Buffers) :
    Executes capture (state v p c (Encoding.frame bits ++ rest) zero one a)
      (work false false c rest zero one a bits []) := by
  have h := capture_exec (state v p c (Encoding.frame bits ++ rest) zero one a)
    bits rest rfl rfl rfl
  have he : afterCapture (state v p c (Encoding.frame bits ++ rest) zero one a) bits rest =
      work false false c rest zero one a bits [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state,work]
  simpa only [he] using h

theorem unframe_work (v p c : Bool) (bits rest zero one : Word) (a : Buffers) :
    Executes unframe (state v p c (Encoding.frame bits ++ rest) zero one a)
      (state false false c (bits ++ rest) zero one a) := by
  have h := unframe_exec (state v p c (Encoding.frame bits ++ rest) zero one a)
    bits rest rfl rfl
  have he : parserState (state v p c (Encoding.frame bits ++ rest) zero one a)
      false false (bits ++ rest) [] = state false false c (bits ++ rest) zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state,work]
  simpa only [he] using h

theorem appendRecord_work (i : Fin 7) (v p c : Bool) (input zero one payload : Word)
    (a : Buffers) :
    Executes (appendRecord 19 (bufferPort i)) (work v p c input zero one a payload [])
      (work false false true input zero one (emit i (record payload) a) payload []) := by
  have h := appendRecord_exec 19 (bufferPort i)
    (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
    (work v p c input zero one a payload []) rfl
  have he : afterRecord (bufferPort i) payload (work v p c input zero one a payload []) =
      work false false true input zero one (emit i (record payload) a) payload [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases i <;> fin_cases j <;>
        simp [work,emit,bufferPort]
  change Executes _ _ (afterRecord (bufferPort i) payload
    (work v p c input zero one a payload [])) at h
  rw [he] at h
  exact h

theorem clearPayload_work (v p c : Bool) (input zero one payload : Word) (a : Buffers) :
    Executes (clear 19) (work v p c input zero one a payload [])
      (state false false c input zero one a) := by
  have h := clear_exec 19 (work v p c input zero one a payload [])
  have he : afterClear 19 (work v p c input zero one a payload []) =
      state false false c input zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [work,readRegs,SubexpHornerProgram.triple]
    · funext i; fin_cases i <;> simp [work,StackRoutines.clearStacks]
  simpa only [he] using h

theorem appendCapturedRecord_work (i : Fin 7) (v p c : Bool)
    (bits rest zero one : Word) (a : Buffers) :
    Executes (appendCapturedRecord (bufferPort i))
      (state v p c (Encoding.frame bits ++ rest) zero one a)
      (state false false true rest zero one (emit i (record bits) a)) :=
  executes_seq (capture_work v p c bits rest zero one a)
    (executes_seq (appendRecord_work i false false c rest zero one bits a)
      (clearPayload_work false false true rest zero one bits (emit i (record bits) a)))

theorem pushBuffer_work (i : Fin 7) (bit v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Executes (pushBit (bufferPort i) bit) (state v p c input zero one a)
      (state bit p c input zero one (Function.update a i (bit :: a i))) := by
  have h := pushBit_exec (bufferPort i) bit (state v p c input zero one a)
  have he : afterPush (bufferPort i) bit (state v p c input zero one a) =
      state bit p c input zero one (Function.update a i (bit :: a i)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state,work,SubexpHornerProgram.triple]
    · funext j; fin_cases i <;> fin_cases j <;> simp [state,work,bufferPort]
  simpa only [he] using h

theorem transferBuffer_work (i : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Executes (transfer (bufferPort i) 19) (state v p c input zero one a)
      (work false false c input zero one (Function.update a i []) (a i).reverse []) := by
  have h := transfer_exec (bufferPort i) 19 (by fin_cases i <;> decide)
    (state v p c input zero one a)
  have he : afterTransfer (bufferPort i) 19 (state v p c input zero one a) =
      work false false c input zero one (Function.update a i []) (a i).reverse [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;>
        simp [state,work,readRegs,SubexpHornerProgram.triple]
    · funext j; fin_cases i <;> fin_cases j <;>
        simp [state,work,StackRoutines.transferStacks,bufferPort]
  simpa only [he] using h

def closeUpdate (i j : Fin 7) (a : Buffers) : Buffers :=
  emit j (record (false :: a i).reverse) (Function.update a i [])

theorem closeInto_work (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Executes (closeInto (bufferPort i) (bufferPort j)) (state v p c input zero one a)
      (state false false true input zero one (closeUpdate i j a)) := by
  let b := Function.update a i (false :: a i)
  have h1 := pushBuffer_work i false v p c input zero one a
  have h2 := transferBuffer_work i false p c input zero one b
  have h3 := appendRecord_work j false false c input zero one (b i).reverse
    (Function.update b i [])
  have h4 := clearPayload_work false false true input zero one (b i).reverse
    (emit j (record (b i).reverse) (Function.update b i []))
  have h := executes_seq h1 (executes_seq h2 (executes_seq h3 h4))
  simpa only [closeInto,closeUpdate,b,Function.update_same,Function.update_idem] using h

theorem appendOne_work_eval (v p c : Bool) (input zero one : Word) (a : Buffers) :
    Eval (appendLiteral 2 13) (8 * one.length + 9) (state v p c input zero one a)
      (state false false true input zero one (emit 0 (SubexpKernelControl.pushWord one) a)) := by
  let ports := triplePorts 2 13 20
  let d := state v p c input zero one a
  let aa : State 3 3 :=
    ⟨SubexpHornerProgram.triple v p c, SubexpHornerProgram.triple one (a 0) []⟩
  let bb : State 3 3 :=
    ⟨SubexpHornerProgram.triple false false true,
      SubexpHornerProgram.triple one
        ((SubexpKernelControl.pushWord one).reverse ++ a 0) []⟩
  have ha : embedState id ports d aa = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id ports d bb =
      state false false true input zero one (emit 0 (SubexpKernelControl.pushWord one) a) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [ports,triplePorts,bb,state,work,emit,
        SubexpHornerProgram.triple]
    · intro i hi
      have h13 : i ≠ 13 := fun h => hi ⟨1,by simpa [ports,triplePorts] using h.symm⟩
      fin_cases i <;> simp_all [state,work,emit,d]
  have h := eval_call_lifted SubexpHornerProgram.Literal.program id ports d
    Function.injective_id (by decide) (a := aa) (b := bb)
    (SubexpHornerProgram.Literal.trace one (a 0) v p c)
  rw [ha,hb] at h
  exact h

theorem appendOne_work (v p c : Bool) (input zero one : Word) (a : Buffers) :
    Executes (appendLiteral 2 13) (state v p c input zero one a)
      (state false false true input zero one (emit 0 (SubexpKernelControl.pushWord one) a)) :=
  ⟨_,appendOne_work_eval v p c input zero one a⟩

theorem transferPayload_work (i : Fin 7) (v p c : Bool)
    (input zero one payload : Word) (a : Buffers) :
    Executes (transfer 19 (bufferPort i)) (work v p c input zero one a payload [])
      (state false false c input zero one (emit i payload a)) := by
  have h := transfer_exec 19 (bufferPort i) (by fin_cases i <;> decide)
    (work v p c input zero one a payload [])
  have he : afterTransfer 19 (bufferPort i) (work v p c input zero one a payload []) =
      state false false c input zero one (emit i payload a) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;>
        simp [work,readRegs,SubexpHornerProgram.triple]
    · funext j; fin_cases i <;> fin_cases j <;>
        simp [work,StackRoutines.transferStacks,bufferPort,emit]
  simpa only [he] using h

theorem reset_work (v p c : Bool) (input zero one payload : Word) (a : Buffers) :
    Executes reset (work v p c input zero one a payload [])
      (work false false false input zero one a payload []) := by
  have h := reset_exec (work v p c input zero one a payload [])
  have he : resetFlags (work v p c input zero one a payload []) =
      work false false false input zero one a payload [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · rfl
  simpa only [he] using h

theorem popTag_work (b v p c : Bool) (rest zero one : Word) (a : Buffers) :
    Executes popTag (state v p c (b :: rest) zero one a)
      (state b true c rest zero one a) := by
  have h := popTag_exec (state v p c (b :: rest) zero one a)
  have he : popped (state v p c (b :: rest) zero one a) =
      state b true c rest zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [state,work,readRegs,SubexpHornerProgram.triple]
    · funext i; fin_cases i <;> simp [state,work]
  simpa only [he] using h

def afterTag {α : Type*} (encode : α → Word) (xs : List α) (rest zero one : Word)
    (c : Bool) (a : Buffers) : Data :=
  match xs with
  | [] => state false true c rest zero one a
  | x :: xs => state true true c
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

theorem popList_work {α : Type*} (encode : α → Word) (xs : List α) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) :
    Executes popTag (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (afterTag encode xs rest zero one c a) := by
  cases xs with
  | nil => simpa [afterTag,Encoding.encodeList] using popTag_work false v p c rest zero one a
  | cons x xs =>
      simpa [afterTag,Encoding.encodeList,List.append_assoc] using popTag_work true v p c
        (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

/-- The ordinary framed-list scan, with its payload body separately proved.
The final assembly theorem instantiates every such body with a fixed program. -/
theorem scan_work {α : Type*} (body : Code) (encode : α → Word)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop)
    (zero one : Word) (vb pb cb : Bool)
    (hbody : ∀ x rest c a, inv a →
      Executes body (state false false c (encode x ++ rest) zero one a)
        (state vb pb cb rest zero one (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (v p c : Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ c', Executes (scan body)
      (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have loop : ∀ (xs : List α) c a, inv a → ∃ c',
      Executes (.while 0 (.seq unframe (.seq body popTag)))
        (afterTag encode xs rest zero one c a)
        (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
    intro xs
    induction xs with
    | nil =>
        intro c a ha
        exact ⟨c,1,Eval.while_false rfl⟩
    | cons x xs ih =>
        intro c a ha
        let tail := Encoding.encodeList encode xs ++ rest
        obtain ⟨n1,h1⟩ := unframe_work true true c (encode x) tail zero one a
        obtain ⟨n2,h2⟩ := hbody x tail c a ha
        obtain ⟨n3,h3⟩ := popList_work encode xs vb pb cb rest zero one (update x a)
        obtain ⟨c',n4,h4⟩ := ih cb (update x a) (hpreserve x a ha)
        refine ⟨c',n1+n2+n3+n4+1,?_⟩
        have hloop := Eval.while_true
          (by rfl : (afterTag encode (x :: xs) rest zero one c a).regs 0 = true)
          (Eval.seq h1 (Eval.seq h2 h3)) h4
        have hcost : (n1 + (n2 + n3)) + n4 + 1 = n1 + n2 + n3 + n4 + 1 := by
          omega
        rw [hcost] at hloop
        exact hloop
  obtain ⟨c',n,h⟩ := loop xs c a ha
  obtain ⟨m,hm⟩ := popList_work encode xs v p c rest zero one a
  exact ⟨c',m+n,Eval.seq hm h⟩

theorem scanFrames_work {α : Type*} (body : Code) (encode : α → Word)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop)
    (zero one : Word) (vb pb cb : Bool)
    (hbody : ∀ x rest c a, inv a →
      Executes body (state true true c (Encoding.frame (encode x) ++ rest) zero one a)
        (state vb pb cb rest zero one (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (v p c : Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ c', Executes (.seq popTag (.while 0 (.seq body popTag)))
      (state v p c (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have loop : ∀ (xs : List α) c a, inv a → ∃ c',
      Executes (.while 0 (.seq body popTag))
        (afterTag encode xs rest zero one c a)
        (state false true c' rest zero one (xs.foldl (fun a x => update x a) a)) := by
    intro xs
    induction xs with
    | nil =>
        intro c a ha
        exact ⟨c,1,Eval.while_false rfl⟩
    | cons x xs ih =>
        intro c a ha
        let tail := Encoding.encodeList encode xs ++ rest
        obtain ⟨n1,h1⟩ := hbody x tail c a ha
        obtain ⟨n2,h2⟩ := popList_work encode xs vb pb cb rest zero one (update x a)
        obtain ⟨c',n3,h3⟩ := ih cb (update x a) (hpreserve x a ha)
        refine ⟨c',n1+n2+n3+1,?_⟩
        exact Eval.while_true rfl (Eval.seq h1 h2) h3
  obtain ⟨c',n,h⟩ := loop xs c a ha
  obtain ⟨m,hm⟩ := popList_work encode xs v p c rest zero one a
  exact ⟨c',m+n,Eval.seq hm h⟩

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
