import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms

namespace OAI.Algorithms

/-!
# An actual clause-row program

The input clause uses `Encoding.encodeList Encoding.encodeNat`. The stored
assignment is an explicit word of the declared length, one bit per variable.
The program parses each literal, decodes its unary index and polarity, performs
a preserving indexed read, and accumulates the disjunction. No semantic test is
an instruction. All auxiliary ports and all input requirements are explicit.
-/

namespace SubexponentialSAT.SubexpClauseRowProgram

open BitProgram StructuredCalls

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

def regs (value present sign acc : Bool) : Fin 4 → Bool :=
  fun i => if i = 0 then value else if i = 1 then present else if i = 2 then sign else acc

@[simp] theorem regs_0 (v p s a : Bool) : regs v p s a 0 = v := rfl
@[simp] theorem regs_1 (v p s a : Bool) : regs v p s a 1 = p := rfl
@[simp] theorem regs_2 (v p s a : Bool) : regs v p s a 2 = s := rfl
@[simp] theorem regs_3 (v p s a : Bool) : regs v p s a 3 = a := rfl
@[simp] theorem regs_update_0 (v p s a b : Bool) :
    Function.update (regs v p s a) 0 b = regs b p s a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_1 (v p s a b : Bool) :
    Function.update (regs v p s a) 1 b = regs v b s a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_2 (v p s a b : Bool) :
    Function.update (regs v p s a) 2 b = regs v p b a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_3 (v p s a b : Bool) :
    Function.update (regs v p s a) 3 b = regs v p s b := by
  funext i; fin_cases i <;> simp [regs]

/-- Array 0; temporary value 1; unary index 2; width 3; array scratch 4--7;
clause source 8; reversed literal payload 9. -/
def tapes (assignment output index width source payload : List Bool) : Fin 10 → List Bool :=
  fun i => if i = 0 then assignment else if i = 1 then output else if i = 2 then index
    else if i = 3 then width else if i = 8 then source else if i = 9 then payload else []

@[simp] theorem stacks_0 (a o i w s p : List Bool) : tapes a o i w s p 0 = a := rfl
@[simp] theorem stacks_1 (a o i w s p : List Bool) : tapes a o i w s p 1 = o := rfl
@[simp] theorem stacks_2 (a o i w s p : List Bool) : tapes a o i w s p 2 = i := rfl
@[simp] theorem stacks_3 (a o i w s p : List Bool) : tapes a o i w s p 3 = w := rfl
@[simp] theorem stacks_8 (a o i w s p : List Bool) : tapes a o i w s p 8 = s := rfl
@[simp] theorem stacks_9 (a o i w s p : List Bool) : tapes a o i w s p 9 = p := rfl
@[simp] theorem stacks_update_1 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 1 x = tapes a x i w s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_2 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 2 x = tapes a o x w s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_3 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 3 x = tapes a o i x s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_8 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 8 x = tapes a o i w x p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_9 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 9 x = tapes a o i w s x := by
  funext j; fin_cases j <;> simp [tapes]

def data (v pr sign acc : Bool) (assignment output index width source payload : List Bool) :
    State 4 10 := ⟨regs v pr sign acc, tapes assignment output index width source payload⟩

namespace LiteralDecoder

/-- Each pair of unary payload bits adds one bit to the index counter. An odd
last bit is the positive-polarity flag. The leading reversed delimiter is consumed. -/
abbrev program : Program 4 10 8 where
  inputStack := 9
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 9 0 1 1
    | 1 => .set 2 false 2
    | 2 => .pop 9 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .bnot 2 2 5
    | 5 => .branch 2 2 6
    | 6 => .push 2 0 2
    | _ => .halt

def cfg (pc : Option (Fin 8)) (v pr sign acc : Bool)
    (assignment output index width source payload : List Bool) : Cfg 4 10 8 :=
  (data v pr sign acc assignment output index width source payload).withPC pc

private theorem pair_cycle (v pr acc : Bool)
    (a o i w src payload : List Bool) :
    Trace program 9 (cfg (some 2) v pr false acc a o i w src (true :: true :: payload))
      (cfg (some 2) true true false acc a o (true :: i) w src payload) := by
  refine .cons (b := cfg (some 3) true true false acc a o i w src (true :: payload)) ?_
    (.cons (b := cfg (some 4) true true false acc a o i w src (true :: payload)) ?_
      (.cons (b := cfg (some 5) true true true acc a o i w src (true :: payload)) ?_
        (.cons (b := cfg (some 2) true true true acc a o i w src (true :: payload)) ?_
          (.cons (b := cfg (some 3) true true true acc a o i w src payload) ?_
            (.cons (b := cfg (some 4) true true true acc a o i w src payload) ?_
              (.cons (b := cfg (some 5) true true false acc a o i w src payload) ?_
                (.cons (b := cfg (some 6) true true false acc a o i w src payload) ?_
                  (.cons ?_ (.refl _)))))))))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem finish_even (v pr acc : Bool) (a o i w src : List Bool) :
    Trace program 3 (cfg (some 2) v pr false acc a o i w src [])
      (cfg none false false false acc a o i w src []) := by
  refine .cons (b := cfg (some 3) false false false acc a o i w src []) ?_
    (.cons (b := cfg (some 7) false false false acc a o i w src []) ?_
      (.cons ?_ (.refl _)))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem finish_odd (v pr acc : Bool) (a o i w src : List Bool) :
    Trace program 7 (cfg (some 2) v pr false acc a o i w src [true])
      (cfg none false false true acc a o i w src []) := by
  refine .cons (b := cfg (some 3) true true false acc a o i w src []) ?_
    (.cons (b := cfg (some 4) true true false acc a o i w src []) ?_
      (.cons (b := cfg (some 5) true true true acc a o i w src []) ?_
        (.cons (b := cfg (some 2) true true true acc a o i w src []) ?_
          (.cons (b := cfg (some 3) false false true acc a o i w src []) ?_
            (.cons (b := cfg (some 7) false false true acc a o i w src []) ?_
              (.cons ?_ (.refl _)))))))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem loop_trace (index : ℕ) (sign v pr acc : Bool)
    (a o i w src : List Bool) :
    Trace program (9 * index + 4 * (if sign then 1 else 0) + 3)
      (cfg (some 2) v pr false acc a o i w src
        (List.replicate (2 * index + if sign then 1 else 0) true))
      (cfg none false false sign acc a o (List.replicate index true ++ i) w src []) := by
  induction index generalizing v pr i with
  | zero => cases sign <;> simpa using (by first | exact finish_even v pr acc a o i w src
                                                       | exact finish_odd v pr acc a o i w src)
  | succ index ih =>
      have h := (pair_cycle v pr acc a o i w src
        (List.replicate (2 * index + if sign then 1 else 0) true)).trans
        (ih true true (true :: i))
      have hcount : 2 * (index + 1) + (if sign then 1 else 0) =
          (2 * index + if sign then 1 else 0) + 2 := by omega
      have hlist : List.replicate index true ++ true :: i =
          List.replicate (index + 1) true ++ i := by
        rw [List.replicate_add]; simp [List.append_assoc]
      convert h using 1 <;> simp [hcount, List.replicate_succ, hlist] ; omega

/-- Exact trace from the reversed canonical natural payload to a unary index
and Boolean polarity. All assignment, clause, and accumulator data are preserved. -/
theorem trace (index : ℕ) (sign v pr oldSign acc : Bool)
    (a o i w src : List Bool) :
    Trace program (9 * index + 4 * (if sign then 1 else 0) + 5)
      (cfg (some program.entry) v pr oldSign acc a o i w src
        (Encoding.encodeNat (2 * index + if sign then 1 else 0)).reverse)
      (cfg none false false sign acc a o (List.replicate index true ++ i) w src []) := by
  have hl := loop_trace index sign false true acc a o i w src
  have h := Computation.Trace.cons
    (a := cfg (some program.entry) v pr oldSign acc a o i w src
      (Encoding.encodeNat (2 * index + if sign then 1 else 0)).reverse)
    (b := cfg (some 1) false true oldSign acc a o i w src
      (List.replicate (2 * index + if sign then 1 else 0) true))
    (by simp [step, cfg, data, execInstr, readRegs, Encoding.encodeNat,
      List.reverse_append, StructuredProgram.State.withPC])
    (Computation.Trace.cons (by simp [step, cfg, data, execInstr,
      StructuredProgram.State.withPC]) hl)
  convert h using 1

end LiteralDecoder


/-- The parser uses only value/present and preserves sign and disjunction. -/
def recordPorts : RecordPrograms.Ports 4 10 where
  tag := 0
  present := 1
  found := 3
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

private theorem record_state (v p sign acc v' p' acc' : Bool)
    (a o i w src payload src' payload' : List Bool) :
    RecordPrograms.state recordPorts (data v p sign acc a o i w src payload)
      v' p' acc' src' payload' = data v' p' sign acc' a o i w src' payload' := by
  simp [RecordPrograms.state, recordPorts, data]

theorem read_literal (bits tail : List Bool) (v p sign acc : Bool)
    (a o i w : List Bool) :
    Eval (RecordPrograms.reader recordPorts) (6 * bits.length + 4)
      (data v p sign acc a o i w (Encoding.frame bits ++ tail) [])
      (data false true sign acc a o i w tail bits.reverse) := by
  have h := RecordPrograms.reader_eval recordPorts
    (data v p sign acc a o i w [] []) bits tail [] v p acc
  simpa only [record_state, List.append_nil] using h

def readStack (i : Fin 8) : Fin 10 := i.castLE (by decide)

theorem readStack_injective : Function.Injective readStack := by
  intro i j h
  apply Fin.ext
  simpa [readStack] using congrArg (fun x : Fin 10 => x.val) h

def readData (v p sign acc : Bool) (a o i w : List Bool) : State 4 8 :=
  ⟨regs v p sign acc, fun j => tapes a o i w [] [] (readStack j)⟩

private theorem embed_read (frame : State 4 10) (v p sign acc : Bool)
    (a o i w src payload : List Bool) (h8 : frame.stacks 8 = src)
    (h9 : frame.stacks 9 = payload) :
    embedState id readStack frame (readData v p sign acc a o i w) =
      data v p sign acc a o i w src payload := by
  apply state_ext
  · funext j
    exact embedState_register id readStack frame _ Function.injective_id j
  · funext j
    by_cases hj : j.val < 8
    · let k : Fin 8 := ⟨j.val, hj⟩
      have hk : readStack k = j := Fin.ext rfl
      rw [← hk, embedState_stack id readStack frame _ readStack_injective]
      simp only [readData, data]
      have h8j : readStack k ≠ 8 := by intro he; have := congrArg Fin.val he; simp [readStack, k] at this; omega
      have h9j : readStack k ≠ 9 := by intro he; have := congrArg Fin.val he; simp [readStack, k] at this; omega
      simp [tapes, h8j, h9j]
    · have hout : ¬ ∃ k, readStack k = j := by
        rintro ⟨k, hk⟩
        have := congrArg Fin.val hk
        simp [readStack] at this
        have := k.isLt
        omega
      rw [embedState_stack_frame id readStack frame _ j hout]
      have hcases : j = 8 ∨ j = 9 := by
        have := j.isLt
        have hv : j.val = 8 ∨ j.val = 9 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hcases with rfl | rfl <;> simp [data, h8, h9]

/-- Persistent single-bit indexed read, with the index represented by its
unary length. The complete source word is restored by the actual array code. -/
abbrev readBit : Cmd 4 10 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 4) 1)
    id readStack)

theorem read_bit (before after out src payload indexWord : List Bool)
    (value v p sign acc : Bool) (hindex : indexWord.length = before.length) :
    Eval readBit (24 * before.length + 31)
      (data v p sign acc (before ++ value :: after) out indexWord [false] src payload)
      (data false false sign acc (before ++ value :: after) (value :: out) [] [false] src payload) := by
  let a := before ++ value :: after
  let d := readData v p sign acc a out indexWord [false]
  have hrows : ∀ row ∈ before.map (fun b => [b]), row.length = [false].length := by
    intro row hr
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
    rfl
  have hflat : (before.map (fun b => [b])).flatten = before := by
    exact List.flatMap_singleton' before
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 4) 1 (by decide)
    (before.map (fun b => [b])) [value] after [false] indexWord d.regs d.stacks
    (by simp [d, readData, readStack, a, hflat])
    (by rfl) (by rfl) (by simpa using hindex) hrows (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  have hr : readRegs d.regs 0 1 none = regs false false sign acc := by
    simp [d, readData, readRegs]
  have hs : ArrayUpdatePrograms.readStacks [value] d.stacks =
      (readData false false sign acc a (value :: out) [] [false]).stacks := by
    funext j
    fin_cases j <;> simp [ArrayUpdatePrograms.readStacks, d, readData, readStack, tapes]
  have ht' : Trace (ArrayUpdatePrograms.readProgram (0 : Fin 4) 1)
      (24 * before.length + 31) (d.withPC (some (ArrayUpdatePrograms.readProgram (0 : Fin 4) 1).entry))
      ((readData false false sign acc a (value :: out) [] [false]).withPC none) := by
    convert ht using 1 <;> simp [StructuredProgram.State.withPC, readData, hr, hs] ; omega
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 4) 1) id readStack
    (data v p sign acc a out indexWord [false] src payload)
    Function.injective_id readStack_injective ht'
  change Eval readBit _
    (embedState id readStack _ d)
    (embedState id readStack _ (readData false false sign acc a (value :: out) [] [false])) at he
  dsimp only [d] at he
  rw [embed_read _ _ _ _ _ _ _ _ _ src payload rfl rfl,
      embed_read _ _ _ _ _ _ _ _ _ src payload rfl rfl] at he
  exact he


theorem read_assignment {n : ℕ} (a : Fin n → Bool) (v : Fin n)
    (out src payload : List Bool) (value present sign acc : Bool) :
    Eval readBit (24 * v.val + 31)
      (data value present sign acc (List.ofFn a) out (List.replicate v.val true) [false] src payload)
      (data false false sign acc (List.ofFn a) (a v :: out) [] [false] src payload) := by
  have hv : v.val < (List.ofFn a).length := by simp
  have hs : List.ofFn a = (List.ofFn a).take v.val ++
      a v :: (List.ofFn a).drop (v.val + 1) := by
    conv_lhs => rw [← List.take_append_drop v.val (List.ofFn a)]
    rw [List.drop_eq_getElem_cons hv]
    simp
  have hl : ((List.ofFn a).take v.val).length = v.val := by
    simp [List.length_take ]
  have h := read_bit ((List.ofFn a).take v.val) ((List.ofFn a).drop (v.val + 1))
    out src payload (List.replicate v.val true) (a v) value present sign acc (by simp [hl])
  simpa only [hl, ← hs] using h

abbrev atom (op : StructuredProgram.Atom 4 10) : Cmd 4 10 := .base (.atom op)

private theorem atom_eval (op : StructuredProgram.Atom 4 10) (a b : State 4 10)
    (h : op.eval a = b) : Eval (atom op) 1 a b := by
  rw [← h]; exact .base (.atom _ _)

/-- One real pop and four Boolean register operations combine a looked-up
variable value with its polarity and the current disjunction. -/
abbrev combine : Cmd 4 10 :=
  .seq (atom (.pop 1 0 1))
    (.seq (atom (.bxor 0 2 0))
      (.seq (atom (.bnot 0 0))
        (.seq (atom (.bor 3 3 0)) (atom (.set 2 false)))))

theorem combine_eval (value v p sign acc : Bool) (a src : List Bool) :
    Eval combine 5 (data v p sign acc a [value] [] [false] src [])
      (data (SubexpFactorProgram.SignedClause.truth sign value) true false
        (acc || SubexpFactorProgram.SignedClause.truth sign value) a [] [] [false] src []) := by
  have h₁ : Eval (atom (.pop 1 0 1)) 1
      (data v p sign acc a [value] [] [false] src [])
      (data value true sign acc a [] [] [false] src []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr, readRegs]
  have h₂ : Eval (atom (.bxor 0 2 0)) 1
      (data value true sign acc a [] [] [false] src [])
      (data (sign ^^ value) true sign acc a [] [] [false] src []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₃ : Eval (atom (.bnot 0 0)) 1
      (data (sign ^^ value) true sign acc a [] [] [false] src [])
      (data (!(sign ^^ value)) true sign acc a [] [] [false] src []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₄ : Eval (atom (.bor 3 3 0)) 1
      (data (!(sign ^^ value)) true sign acc a [] [] [false] src [])
      (data (!(sign ^^ value)) true sign (acc || !(sign ^^ value)) a [] [] [false] src []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₅ : Eval (atom (.set 2 false)) 1
      (data (!(sign ^^ value)) true sign (acc || !(sign ^^ value)) a [] [] [false] src [])
      (data (!(sign ^^ value)) true false (acc || !(sign ^^ value)) a [] [] [false] src []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  exact h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))

abbrev literalCmd : Cmd 4 10 :=
  .seq (RecordPrograms.reader recordPorts)
    (.seq (.call LiteralDecoder.program) (.seq readBit combine))

/-- Full literal pipeline: framed bytes to index and polarity, then an actual
restoring array lookup and Boolean evaluation. -/
theorem literal_eval {n : ℕ} (a : Fin n → Bool) (l : SAT.Literal (Fin n))
    (tail : List Bool) (v p sign acc : Bool) :
    Eval literalCmd (45 * l.variable.val + 10 * (if l.positive then 1 else 0) + 51)
      (data v p sign acc (List.ofFn a) [] [] [false]
        (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++ tail) [])
      (data (l.eval a) true false (acc || l.eval a) (List.ofFn a) [] [] [false] tail []) := by
  have h₁ := read_literal (Encoding.encodeNat (Encoding.literalCode l)) tail v p sign acc
    (List.ofFn a) [] [] [false]
  have h₂ : Eval (.call LiteralDecoder.program)
      (9 * l.variable.val + 4 * (if l.positive then 1 else 0) + 5)
      (data false true sign acc (List.ofFn a) [] [] [false] tail
        (Encoding.encodeNat (Encoding.literalCode l)).reverse)
      (data false false l.positive acc (List.ofFn a) []
        (List.replicate l.variable.val true) [false] tail []) := by
    apply Eval.call
    simpa only [LiteralDecoder.cfg, Encoding.literalCode, List.append_nil] using
      LiteralDecoder.trace l.variable.val l.positive false true sign acc
        (List.ofFn a) [] [] [false] tail
  have h₃ := read_assignment a l.variable [] tail [] false false l.positive acc
  have h₄ := combine_eval (a l.variable) false false l.positive acc (List.ofFn a) tail
  have ht := h₁.seq (h₂.seq (h₃.seq h₄))
  convert ht using 1
  · cases hp : l.positive <;> simp [Encoding.encodeNat, Encoding.literalCode, hp] <;> omega
  · rw [SubexpFactorProgram.SignedClause.truth_eq_eval]

def clauseBytes {n : ℕ} (ls : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList Encoding.encodeNat (ls.map Encoding.literalCode)

def afterTag {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (acc : Bool) (suffix : List Bool) : State 4 10 :=
  match ls with
  | [] => data false true false acc (List.ofFn a) [] [] [false] suffix []
  | l :: rest => data true true false acc (List.ofFn a) [] [] [false]
      (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
        (clauseBytes rest ++ suffix)) []

theorem pop_tag {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (acc v p : Bool) (suffix : List Bool) :
    Eval (atom (.pop 8 0 1)) 1
      (data v p false acc (List.ofFn a) [] [] [false] (clauseBytes ls ++ suffix) [])
      (afterTag a ls acc suffix) := by
  apply atom_eval
  cases ls <;> simp [afterTag, clauseBytes, Encoding.encodeList,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, data, execInstr, readRegs]

abbrev rowLoop : Cmd 4 10 := .while 0 (.seq literalCmd (atom (.pop 8 0 1)))

def rowCost {n : ℕ} : List (SAT.Literal (Fin n)) → ℕ
  | [] => 0
  | l :: rest => 45 * l.variable.val + 10 * (if l.positive then 1 else 0) + 53 + rowCost rest

/-- Every input literal is visited; the loop cost includes each actual branch.
The complete stored assignment is preserved through all indexed reads. -/
theorem row_loop_eval {n : ℕ} (a : Fin n → Bool)
    (ls : List (SAT.Literal (Fin n))) (acc : Bool) (suffix : List Bool) :
    Eval rowLoop (rowCost ls + 1) (afterTag a ls acc suffix)
      (data false true false (acc || ls.any (fun l => l.eval a))
        (List.ofFn a) [] [] [false] suffix []) := by
  induction ls generalizing acc with
  | nil =>
      simpa [rowLoop, rowCost, afterTag] using
        (Eval.while_false (test := (0 : Fin 4))
          (body := .seq literalCmd (atom (.pop 8 0 1)))
          (a := afterTag a [] acc suffix) rfl)
  | cons l rest ih =>
      have h₁ := literal_eval a l (clauseBytes rest ++ suffix) true true false acc
      have h₂ := pop_tag a rest (acc || l.eval a) (l.eval a) true suffix
      have h₃ := ih (acc || l.eval a)
      have ht := Eval.while_true (test := (0 : Fin 4)) rfl (h₁.seq h₂) h₃
      convert ht using 1 <;> simp [ rowCost, afterTag, Bool.or_assoc] ; omega


abbrev clearRegisters : Cmd 4 10 :=
  .seq (atom (.set 0 false)) (.seq (atom (.set 1 false))
    (.seq (atom (.set 2 false)) (atom (.set 3 false))))

private theorem clear_registers_eval (v p sign acc : Bool)
    (a o i w src payload : List Bool) :
    Eval clearRegisters 4 (data v p sign acc a o i w src payload)
      (data false false false false a o i w src payload) := by
  have h₁ : Eval (atom (.set 0 false)) 1 (data v p sign acc a o i w src payload)
      (data false p sign acc a o i w src payload) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₂ : Eval (atom (.set 1 false)) 1 (data false p sign acc a o i w src payload)
      (data false false sign acc a o i w src payload) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₃ : Eval (atom (.set 2 false)) 1 (data false false sign acc a o i w src payload)
      (data false false false acc a o i w src payload) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₄ : Eval (atom (.set 3 false)) 1 (data false false false acc a o i w src payload)
      (data false false false false a o i w src payload) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  exact h₁.seq (h₂.seq (h₃.seq h₄))

abbrev setup : Cmd 4 10 :=
  .seq clearRegisters (.seq (atom (.push 3 0)) (atom (.pop 8 0 1)))

theorem setup_eval {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (v p sign acc : Bool) (suffix : List Bool) :
    Eval setup 6
      (data v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) [])
      (afterTag a ls false suffix) := by
  have h₁ := clear_registers_eval v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) []
  have h₂ : Eval (atom (.push 3 0)) 1
      (data false false false false (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) [])
      (data false false false false (List.ofFn a) [] [] [false] (clauseBytes ls ++ suffix) []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  exact h₁.seq (h₂.seq (pop_tag a ls false false false suffix))

abbrev finish : Cmd 4 10 :=
  .seq (atom (.push 1 3)) (.seq (atom (.pop 3 0 1))
    (.seq (atom (.set 1 false)) (atom (.set 3 false))))

theorem finish_eval (answer : Bool) (a suffix : List Bool) :
    Eval finish 4 (data false true false answer a [] [] [false] suffix [])
      (data false false false false a [answer] [] [] suffix []) := by
  have h₁ : Eval (atom (.push 1 3)) 1
      (data false true false answer a [] [] [false] suffix [])
      (data false true false answer a [answer] [] [false] suffix []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₂ : Eval (atom (.pop 3 0 1)) 1
      (data false true false answer a [answer] [] [false] suffix [])
      (data false true false answer a [answer] [] [] suffix []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr, readRegs]
  have h₃ : Eval (atom (.set 1 false)) 1
      (data false true false answer a [answer] [] [] suffix [])
      (data false false false answer a [answer] [] [] suffix []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  have h₄ : Eval (atom (.set 3 false)) 1
      (data false false false answer a [answer] [] [] suffix [])
      (data false false false false a [answer] [] [] suffix []) := by
    apply atom_eval
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, data, execInstr]
  exact h₁.seq (h₂.seq (h₃.seq h₄))

/-- The fixed command prepares its width counter, traverses the clause, and
emits exactly one Boolean result. The assignment and trailing source are framed. -/
abbrev command : Cmd 4 10 := .seq setup (.seq rowLoop finish)

theorem eval {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (v p sign acc : Bool) (suffix : List Bool) :
    Eval command (rowCost ls + 11)
      (data v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) [])
      (data false false false false (List.ofFn a) [ls.any (fun l => l.eval a)] [] [] suffix []) := by
  have h₁ := setup_eval a ls v p sign acc suffix
  have h₂ := row_loop_eval a ls false suffix
  have h₃ := finish_eval (ls.any (fun l => l.eval a)) (List.ofFn a) suffix
  simp only [Bool.false_or] at h₂
  convert h₁.seq (h₂.seq h₃) using 1 ; omega

abbrev program : Program 4 10 (size command + 1) := compiled command 8 1

/-- A complete finite instruction trace, including halt. -/
theorem trace {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (v p sign acc : Bool) (suffix : List Bool) :
    Trace program (rowCost ls + 12)
      ((data v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) []).withPC
        (some program.entry))
      ((data false false false false (List.ofFn a) [ls.any (fun l => l.eval a)] [] [] suffix []).withPC none) := by
  simpa only [Nat.add_assoc] using compiled_halt_trace (eval a ls v p sign acc suffix) 8 1

/-- In particular the exact finite-set clause semantics is computed, even if
the supplied literal list has duplicates. -/
theorem clause_trace {n : ℕ} (a : Fin n → Bool) (ls : List (SAT.Literal (Fin n)))
    (C : SAT.Clause (Fin n)) (hls : ls.toFinset = C)
    (v p sign acc : Bool) (suffix : List Bool) :
    Trace program (rowCost ls + 12)
      ((data v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) []).withPC
        (some program.entry))
      ((data false false false false (List.ofFn a) [C.eval a] [] [] suffix []).withPC none) := by
  have he : ls.any (fun l => l.eval a) = C.eval a := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, SAT.Clause.eval_eq_true]
    simp only [← hls, List.mem_toFinset]
  simpa only [he] using trace a ls v p sign acc suffix

/-- The bound is polynomial in the explicit declared variable count and
number of input literal records, including unary index parsing and lookup. -/
theorem rowCost_le {n : ℕ} (ls : List (SAT.Literal (Fin n))) :
    rowCost ls ≤ (45 * n + 63) * ls.length := by
  induction ls with
  | nil => simp [rowCost]
  | cons l rest ih =>
      have hv : l.variable.val ≤ n := Nat.le_of_lt l.variable.isLt
      have hm := Nat.mul_le_mul_left 45 hv
      have hb : (if l.positive then 1 else 0) ≤ 1 := by cases l.positive <;> decide
      have hs := Nat.mul_le_mul_left 10 hb
      simp only [rowCost, List.length_cons]
      nlinarith

theorem primitive_execution {n : ℕ} (a : Fin n → Bool)
    (ls : List (SAT.Literal (Fin n))) (v p sign acc : Bool) (suffix : List Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (rowCost ls + 12))
      (BitProgram.primitiveCfg program
        ((data v p sign acc (List.ofFn a) [] [] [] (clauseBytes ls ++ suffix) []).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data false false false false (List.ofFn a) [ls.any (fun l => l.eval a)] [] [] suffix []).withPC none)) :=
  BitProgram.primitive_trace program (trace a ls v p sign acc suffix)


/-- The whole evaluator has fixed control independently of `n`, clause size,
and the values of its literal indices. -/
theorem control_size : size command + 1 = 71 := rfl

/-- Interpret an explicit word of the declared length as an assignment. -/
def wordAssignment {n : ℕ} (word : List Bool) (hlen : word.length = n) : Fin n → Bool :=
  fun v => word[v.val]'(by simpa only [hlen] using v.isLt)

theorem ofFn_wordAssignment {n : ℕ} (word : List Bool) (hlen : word.length = n) :
    List.ofFn (wordAssignment word hlen) = word := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [wordAssignment]

/-- Convenient execution contract for an already materialized assignment word.
The four caller register values are unrestricted. -/
theorem eval_word {n : ℕ} (word : List Bool) (hlen : word.length = n)
    (ls : List (SAT.Literal (Fin n))) (v p sign acc : Bool) (suffix : List Bool) :
    Eval command (rowCost ls + 11)
      (data v p sign acc word [] [] [] (clauseBytes ls ++ suffix) [])
      (data false false false false word
        [ls.any (fun l => l.eval (wordAssignment word hlen))] [] [] suffix []) := by
  simpa only [ofFn_wordAssignment] using
    eval (wordAssignment word hlen) ls v p sign acc suffix

section FactorSemantics

variable {n : ℕ} {J A : Type*} [DecidableEq J] [DecidableEq A] {b : J → ℕ}

/-- The fully indexed row program computes the actual constructed clause
factor on valid encoded chunk labels. Its input assignment is the materialized
concatenation specified by `positions`; building that word is a separate trace. -/
theorem factor_trace
    (positions : Fin n ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF (Fin n))
    (C : {C // C ∈ F}) (x : (j : J) → Fin (b j) → Bool)
    (ls : List (SAT.Literal (Fin n))) (hls : ls.toFinset = C.val)
    (v p sign acc : Bool) (suffix : List Bool) :
    Trace program (rowCost ls + 12)
      ((data v p sign acc (List.ofFn (FactorReduction.assignmentFromChunks positions x))
        [] [] [] (clauseBytes ls ++ suffix) []).withPC (some program.entry))
      ((data false false false false
        (List.ofFn (FactorReduction.assignmentFromChunks positions x))
        [Factor.evalFactor (FactorReduction.cnfFactorSystem positions enc F) (.inr C)
          (FactorReduction.encode enc x)] [] [] suffix []).withPC none) := by
  have hf : Factor.evalFactor (FactorReduction.cnfFactorSystem positions enc F) (.inr C)
      (FactorReduction.encode enc x) =
      FactorReduction.cnfTable positions F C (fun j => x j.val) :=
    SubexpFactorProgram.factorTable_on_encoding enc (FactorReduction.cnfScope positions F)
      (FactorReduction.cnfTable positions F) C (fun j => x j.val)
  have ht : FactorReduction.cnfTable positions F C (fun j => x j.val) =
      C.val.eval (FactorReduction.assignmentFromChunks positions x) :=
    Bool.eq_iff_iff.mpr (FactorReduction.cnfTable_true_iff positions F C x)
  rw [hf, ht]
  exact clause_trace (FactorReduction.assignmentFromChunks positions x) ls C.val hls v p sign acc suffix

end FactorSemantics

end SubexponentialSAT.SubexpClauseRowProgram

end OAI.Algorithms
