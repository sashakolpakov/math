import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedFactorProgram

namespace OAI.Algorithms

/-! Concrete parser, scalar-literal, and output services for prepared factors. -/

namespace SubexponentialSAT.SubexpPreparedFactor

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

private theorem parserRegs_injective : Function.Injective parserRegs := Fin.castAdd_injective _ _
private theorem parserPorts_injective : Function.Injective parserPorts := by decide
private theorem scalarPorts_injective : Function.Injective scalarPorts := Fin.castAdd_injective _ _

theorem stores_buffer (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch : Word) (i : Fin 3) :
    stores D input scalar a parser payload scratch (bufferPort i) = a i := by
  fin_cases i <;> rfl

theorem stores_payload (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch : Word) : stores D input scalar a parser payload scratch 19 = payload := rfl

theorem stores_update_buffer (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch : Word) (i : Fin 3) (bits : Word) :
    Function.update (stores D input scalar a parser payload scratch) (bufferPort i) bits =
      stores D input scalar (Function.update a i bits) parser payload scratch := by
  fin_cases i
  · change Function.update (stores D input scalar a parser payload scratch) (15 : Fin 22) bits =
      stores D input scalar (Function.update a 0 bits) parser payload scratch
    funext j
    by_cases hj : j = 15
    · subst j; simp [stores]
    · rw [Function.update_of_ne hj]
      simp only [stores,Function.update_self,Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide),hj,ite_false]
  · change Function.update (stores D input scalar a parser payload scratch) (16 : Fin 22) bits =
      stores D input scalar (Function.update a 1 bits) parser payload scratch
    funext j
    by_cases hj : j = 16
    · subst j; simp [stores]
    · rw [Function.update_of_ne hj]
      simp only [stores,Function.update_self,Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),hj,ite_false]
  · change Function.update (stores D input scalar a parser payload scratch) (17 : Fin 22) bits =
      stores D input scalar (Function.update a 2 bits) parser payload scratch
    funext j
    by_cases hj : j = 17
    · subst j; simp [stores]
    · rw [Function.update_of_ne hj]
      simp only [stores,Function.update_self,Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
        Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide),hj,ite_false]

theorem stores_update_payload (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch bits : Word) :
    Function.update (stores D input scalar a parser payload scratch) 19 bits =
      stores D input scalar a parser bits scratch := by
  funext j
  by_cases hj : j = 19 <;> simp [stores, hj]

private def parserData (r : Fin 5 → Bool) (input : Word) : State 2 2 :=
  ⟨ParserProgram.pair (r 0) (r 1), ParserProgram.pair input []⟩

theorem unframe_eval (r : Fin 5 → Bool) (D : ℕ) (bits rest : Word) (a : Buffers) :
    Eval unframe (9 * bits.length + 7)
      (ready r D (Encoding.frame bits ++ rest) a)
      (ready (readRegs r 0 1 none) D (bits ++ rest) a) := by
  let start := ready r D (Encoding.frame bits ++ rest) a
  let finish := ready (readRegs r 0 1 none) D (bits ++ rest) a
  have ha : embedState parserRegs parserPorts start
      (parserData r (Encoding.frame bits ++ rest)) = start := by
    apply embedState_eq_of_ports _ _ _ _ _ parserRegs_injective parserPorts_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [start,ready,work,stores,parserPorts,parserData,ParserProgram.pair]
    · intros; rfl
  have hb : embedState parserRegs parserPorts start
      (parserData (readRegs r 0 1 none) (bits ++ rest)) = finish := by
    apply embedState_eq_of_ports _ _ _ _ _ parserRegs_injective parserPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      simp [start,finish,ready,work,readRegs,h0,h1]
    · intro i; fin_cases i <;> simp [finish,ready,work,stores,parserPorts,parserData,ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      simp only [start,finish,ready,work,stores,h0,ite_false]
  have h := eval_call_lifted ParserProgram.unframeProgram parserRegs parserPorts start
    parserRegs_injective parserPorts_injective
    (a := parserData r (Encoding.frame bits ++ rest))
    (b := parserData (readRegs r 0 1 none) (bits ++ rest))
    (ParserProgram.unframe_trace bits rest (r 0) (r 1))
  rw [ha,hb] at h
  exact h

private theorem capturePorts_injective (i : Fin 3) :
    Function.Injective (capturePorts (bufferPort i)) := by
  intro j k h
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [capturePorts,bufferPort]

private def captureData (r : Fin 5 → Bool) (input output : Word) : State 2 3 :=
  ⟨ParserProgram.pair (r 0) (r 1), ExecCNFRecords.ports input [] output⟩

theorem captureFrame_eval (i : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (bits rest : Word) (a : Buffers) :
    Eval (captureFrame (bufferPort i)) (7 * bits.length + 5)
      (ready r D (Encoding.frame bits ++ rest) a)
      (ready (readRegs r 0 1 (some false)) D rest (emit i (Encoding.frame bits) a)) := by
  let start := ready r D (Encoding.frame bits ++ rest) a
  let finish := ready (readRegs r 0 1 (some false)) D rest (emit i (Encoding.frame bits) a)
  have hs := capturePorts_injective i
  have ha : embedState parserRegs (capturePorts (bufferPort i)) start
      (captureData r (Encoding.frame bits ++ rest) (a i)) = start := by
    apply embedState_eq_of_ports _ _ _ _ _ parserRegs_injective hs
    · intro j; fin_cases j <;> rfl
    · intros; rfl
    · intro j; fin_cases i <;> fin_cases j <;>
        simp [captureData,capturePorts,start,ready,work,stores,bufferPort,ExecCNFRecords.ports]
    · intros; rfl
  have hb : embedState parserRegs (capturePorts (bufferPort i)) start
      (captureData (readRegs r 0 1 (some false)) rest
        ((Encoding.frame bits).reverse ++ a i)) = finish := by
    apply embedState_eq_of_ports _ _ _ _ _ parserRegs_injective hs
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1,h.symm⟩
      simp [start,finish,ready,work,readRegs,h0,h1]
    · intro j; fin_cases i <;> fin_cases j <;>
        simp [captureData, capturePorts, finish, ready, work, stores, bufferPort, emit,
          ExecCNFRecords.ports]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,h.symm⟩
      have hb : j ≠ bufferPort i := fun h => hj ⟨2,h.symm⟩
      fin_cases i <;> simp_all [start,finish,ready,work,stores,emit,bufferPort]
  have ht := ExecCNFRecords.capture_frame_trace bits rest [] (a i) (r 0) (r 1)
  have h := eval_call_lifted captureBody parserRegs (capturePorts (bufferPort i)) start
    parserRegs_injective hs
    (a := captureData r (Encoding.frame bits ++ rest) (a i))
    (b := captureData (readRegs r 0 1 (some false)) rest
      ((Encoding.frame bits).reverse ++ a i)) ht
  rw [ha,hb] at h
  exact h

private theorem flags_eta (r : Fin 5 → Bool) :
    SubexpArgumentEmitLoop.flags (r 0) (r 1) (r 2) (r 3) (r 4) = r := by
  funext i; fin_cases i <;> rfl

def scalarRegs (r : Fin 5 → Bool) : Fin 5 → Bool :=
  SubexpArgumentEmitLoop.flags true false false false (r 4)

private theorem embed_scalar (r : Fin 5 → Bool) (v p m u s : Bool) (D : ℕ)
    (input scalar input' scalar' : Word) (a : Buffers) :
    embedState id scalarPorts (work r D input scalar a [] [] [])
      (SubexpArgumentEmitLoop.ready v p m u s input' scalar'
        D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0) =
      work (SubexpArgumentEmitLoop.flags v p m u s) D input' scalar' a [] [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalarPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3,h.symm⟩
    simp only [work,stores,h0,h3,ite_false]

theorem scalar_eval (r : Fin 5 → Bool) (D : ℕ) (coefficient rest : Word) (a : Buffers) :
    Eval scalar
      (SubexpArgumentEmitLoop.constantCost D (SubexpSymbolicCost.indexBits D) false coefficient + 1)
      (work r D (Encoding.frame coefficient ++ rest) [false] a [] [] [])
      (work (scalarRegs r) D rest (SubexpScalarLiteralProgram.rawLiteral D coefficient) a [] [] []) := by
  have h := eval_call_lifted SubexpScalarLiteralProgram.program id scalarPorts
    (work r D (Encoding.frame coefficient ++ rest) [false] a [] [] [])
    Function.injective_id scalarPorts_injective
    (SubexpScalarLiteralProgram.program_trace D coefficient rest (r 0) (r 1) (r 2) (r 3) (r 4))
  simpa only [scalar,embed_scalar,flags_eta,scalarRegs] using h

theorem pushScalar_eval (r : Fin 5 → Bool) (D : ℕ) (input : Word) (a : Buffers) :
    Eval (pushBit 3 false) 2 (ready r D input a)
      (work (Function.update r 0 false) D input [false] a [] [] []) := by
  have h := pushBit_eval 3 false (ready r D input a)
  have hf : afterPush 3 false (ready r D input a) =
      work (Function.update r 0 false) D input [false] a [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases hj : j = 3 <;> simp [ready, work, stores, Function.update_apply, hj]
  rw [hf] at h
  exact h

theorem clearScalar_eval (r : Fin 5 → Bool) (D : ℕ) (input bits : Word) (a : Buffers) :
    Eval (clear 3) (2 * bits.length + 3) (work r D input bits a [] [] [])
      (ready (readRegs r 0 1 none) D input a) := by
  have h := clear_eval 3 (work r D input bits a [] [] [])
  have hf : afterClear 3 (work r D input bits a [] [] []) =
      ready (readRegs r 0 1 none) D input a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases hj : j = 3 <;>
        simp [work, stores, StackRoutines.clearStacks, Function.update_apply, hj]
  rw [hf] at h
  have hl : (work r D input bits a [] [] []).stacks 3 = bits := by simp [work,stores]
  simpa only [hl] using h

def framed (tag : Bool) (bits : Word) : Word := if tag then record bits else Encoding.frame bits

theorem frameScalar_eval (tag : Bool) (i : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (input bits : Word) (a : Buffers) :
    Eval (if tag then appendRecord 3 (bufferPort i) else appendFrame 3 (bufferPort i))
      (8 * bits.length + if tag then 10 else 8)
      (work r D input bits a [] [] [])
      (work (frameRegs r) D input bits (emit i (framed tag bits) a) [] [] []) := by
  cases tag with
  | false =>
      have h := appendFrame_eval 3 (bufferPort i) (by fin_cases i <;> decide)
        (by decide) (by fin_cases i <;> decide) (work r D input bits a [] [] []) (by simp [work,stores])
      have hf : afterFrame (bufferPort i) bits (work r D input bits a [] [] []) =
          work (frameRegs r) D input bits (emit i (Encoding.frame bits) a) [] [] [] := by
        apply congrArg₂ StructuredProgram.State.mk
        · rfl
        · change Function.update (stores D input bits a [] [] []) (bufferPort i)
            ((Encoding.frame bits).reverse ++ stores D input bits a [] [] [] (bufferPort i)) = _
          rw [stores_buffer,stores_update_buffer]
          rfl
      have hl : (work r D input bits a [] [] []).stacks 3 = bits := by simp [work,stores]
      rw [hl,hf] at h
      exact h
  | true =>
      have h := appendRecord_eval 3 (bufferPort i) (by fin_cases i <;> decide)
        (by decide) (by fin_cases i <;> decide) (work r D input bits a [] [] []) (by simp [work,stores])
      have hf : afterRecord (bufferPort i) bits (work r D input bits a [] [] []) =
          work (frameRegs r) D input bits (emit i (record bits) a) [] [] [] := by
        apply congrArg₂ StructuredProgram.State.mk
        · rfl
        · change Function.update (stores D input bits a [] [] []) (bufferPort i)
            ((record bits).reverse ++ stores D input bits a [] [] [] (bufferPort i)) = _
          rw [stores_buffer,stores_update_buffer]
          rfl
      have hl : (work r D input bits a [] [] []).stacks 3 = bits := by simp [work,stores]
      rw [hl,hf] at h
      exact h

def scalarCost (D : ℕ) (tag : Bool) (bits : Word) : ℕ :=
  2 + ((SubexpArgumentEmitLoop.constantCost D (SubexpSymbolicCost.indexBits D) false bits + 1) +
    ((8 * (SubexpScalarLiteralProgram.rawLiteral D bits).length + if tag then 10 else 8) +
      (2 * (SubexpScalarLiteralProgram.rawLiteral D bits).length + 3)))

theorem emitScalar_eval (tag : Bool) (i : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (bits rest : Word) (a : Buffers) :
    ∃ r', Eval (emitScalar (bufferPort i) tag) (scalarCost D tag bits)
      (ready r D (Encoding.frame bits ++ rest) a)
      (ready r' D rest (emit i (framed tag (SubexpScalarLiteralProgram.rawLiteral D bits)) a)) := by
  have h1 := pushScalar_eval r D (Encoding.frame bits ++ rest) a
  have h2 := scalar_eval (Function.update r 0 false) D bits rest a
  have h3 := frameScalar_eval tag i (scalarRegs (Function.update r 0 false)) D rest
    (SubexpScalarLiteralProgram.rawLiteral D bits) a
  have h4 := clearScalar_eval (frameRegs (scalarRegs (Function.update r 0 false))) D rest
    (SubexpScalarLiteralProgram.rawLiteral D bits)
    (emit i (framed tag (SubexpScalarLiteralProgram.rawLiteral D bits)) a)
  exact ⟨_,h1.seq (h2.seq (h3.seq h4))⟩

theorem pushBuffer_eval (i : Fin 3) (b : Bool) (r : Fin 5 → Bool) (D : ℕ)
    (input : Word) (a : Buffers) :
    Eval (pushBit (bufferPort i) b) 2 (ready r D input a)
      (ready (Function.update r 0 b) D input (Function.update a i (b :: a i))) := by
  have h := pushBit_eval (bufferPort i) b (ready r D input a)
  have hf : afterPush (bufferPort i) b (ready r D input a) =
      ready (Function.update r 0 b) D input (Function.update a i (b :: a i)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change Function.update (stores D input [] a [] [] []) (bufferPort i)
        (b :: stores D input [] a [] [] [] (bufferPort i)) = _
      rw [stores_buffer,stores_update_buffer]
  rw [hf] at h
  exact h

theorem drainBuffer_eval (i : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (input : Word) (a : Buffers) :
    Eval (transfer (bufferPort i) 19) (3 * (a i).length + 3)
      (ready r D input a)
      (work (readRegs r 0 1 none) D input [] (Function.update a i []) [] (a i).reverse []) := by
  have h := transfer_eval (bufferPort i) 19 (by fin_cases i <;> decide) (ready r D input a)
  have hf : afterTransfer (bufferPort i) 19 (ready r D input a) =
      work (readRegs r 0 1 none) D input [] (Function.update a i []) [] (a i).reverse [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change StackRoutines.transferStacks (bufferPort i) 19 (stores D input [] a [] [] []) = _
      unfold StackRoutines.transferStacks
      rw [stores_buffer,stores_payload,stores_update_buffer,stores_update_payload,List.append_nil]
  rw [hf] at h
  have hl : ((ready r D input a).stacks (bufferPort i)).length = (a i).length := by
    fin_cases i <;> simp [ready,work,stores,bufferPort]
  simpa only [hl] using h

theorem framePayload_eval (i : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (input bits : Word) (a : Buffers) :
    Eval (appendRecord 19 (bufferPort i)) (8 * bits.length + 10)
      (work r D input [] a [] bits [])
      (work (frameRegs r) D input [] (emit i (record bits) a) [] bits []) := by
  have h := appendRecord_eval 19 (bufferPort i) (by fin_cases i <;> decide)
    (by decide) (by fin_cases i <;> decide) (work r D input [] a [] bits []) (by simp [work,stores])
  have hf : afterRecord (bufferPort i) bits (work r D input [] a [] bits []) =
      work (frameRegs r) D input [] (emit i (record bits) a) [] bits [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change Function.update (stores D input [] a [] bits []) (bufferPort i)
        ((record bits).reverse ++ stores D input [] a [] bits [] (bufferPort i)) = _
      rw [stores_buffer,stores_update_buffer]
      rfl
  have hl : (work r D input [] a [] bits []).stacks 19 = bits := by simp [work,stores]
  rw [hl,hf] at h
  exact h

theorem clearPayload_eval (r : Fin 5 → Bool) (D : ℕ) (input bits : Word) (a : Buffers) :
    Eval (clear 19) (2 * bits.length + 3) (work r D input [] a [] bits [])
      (ready (readRegs r 0 1 none) D input a) := by
  have h := clear_eval 19 (work r D input [] a [] bits [])
  have hf : afterClear 19 (work r D input [] a [] bits []) =
      ready (readRegs r 0 1 none) D input a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases hj : j = 19 <;>
        simp [work, stores, StackRoutines.clearStacks, Function.update_apply, hj]
  rw [hf] at h
  have hl : (work r D input [] a [] bits []).stacks 19 = bits := by simp [work,stores]
  simpa only [hl] using h

def closeUpdate (i j : Fin 3) (a : Buffers) : Buffers :=
  emit j (record ((false :: a i).reverse)) (Function.update a i [])

theorem closeInto_eval (i j : Fin 3) (r : Fin 5 → Bool) (D : ℕ)
    (input : Word) (a : Buffers) :
    ∃ r', Eval (closeInto (bufferPort i) (bufferPort j)) (13 * ((a i).length + 1) + 18)
      (ready r D input a) (ready r' D input (closeUpdate i j a)) := by
  let a1 := Function.update a i (false :: a i)
  have h1 := pushBuffer_eval i false r D input a
  have h2 := drainBuffer_eval i (Function.update r 0 false) D input a1
  simp only [a1,Function.update_same,Function.update_idem] at h2
  have h3 := framePayload_eval j (readRegs (Function.update r 0 false) 0 1 none) D input
    (false :: a i).reverse (Function.update a i [])
  have h4 := clearPayload_eval (frameRegs (readRegs (Function.update r 0 false) 0 1 none)) D input
    (false :: a i).reverse (closeUpdate i j a)
  refine ⟨readRegs (frameRegs (readRegs (Function.update r 0 false) 0 1 none)) 0 1 none,?_⟩
  have h := h1.seq (h2.seq (h3.seq h4))
  have hcost :
      2 + ((3 * (false :: a i).length + 3) +
        ((8 * (false :: a i).reverse.length + 10) +
          (2 * (false :: a i).reverse.length + 3))) =
        13 * ((a i).length + 1) + 18 := by
    simp only [List.length_reverse, List.length_cons]
    omega
  rw [hcost] at h
  simpa only [closeInto] using h

end SubexponentialSAT.SubexpPreparedFactor

end OAI.Algorithms
