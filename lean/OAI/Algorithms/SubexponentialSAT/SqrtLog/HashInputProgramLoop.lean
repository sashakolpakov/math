import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopTerm

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev term : Cmd 8 24 := .seq decode (.seq lookup (.seq copyShape
  (.seq normalize (.seq frameWeight (.seq frameRecord tagRecord)))))

def termBudget (b ml m sourceLength weightLength clauseLength : ℕ) : ℕ :=
  LoopDecode.budget b ml m + 9*b+8 +
  (23*sourceLength+19) + (7*weightLength+5) +
  (7*weightLength+2*b+9) + (7*weightLength+10) +
  (7*(2*weightLength+1+clauseLength)+10) + 2

def payload (t d : ℕ) (clauses : List (List Bool))
    (a : Fin clauses.length × ZMod 3) : List Bool :=
  Encoding.frame (RingProgram.flat (constantVector t d a.2)) ++ clauses[a.1.val]

theorem flat_length (t d : ℕ) (c : ZMod 3) :
    (RingProgram.flat (constantVector t d c)).length =
      (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t := by
  exact RingProgram.flat_length (constantVector t d c)

theorem term_eval (t d : ℕ) (ht : 0 < t) (clauses : List (List Bool))
    (a : Fin clauses.length × ZMod 3) (regs : Fin 8 → Bool)
    (word rest width modulus shape acc : List Bool)
    (hw : width.length=word.length)
    (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    (hword : SubexponentialSAT.BinaryArithmetic.toNat word=a.1.val+clauses.length*a.2.val) :
    ∃ n ≤ termBudget word.length modulus.length clauses.length
        (Encoding.encodeList id clauses).length shape.length clauses[a.1.val].length,
      ∃ rf, Eval term n
        (data regs (word.reverse++rest) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
        (data rf rest width modulus (Encoding.encodeList id clauses) shape
          (true::(Encoding.frame (payload t d clauses a)++acc)) [] [] [] []) := by
  have hmpos : 0 < clauses.length := lt_of_le_of_lt (Nat.zero_le _) a.1.isLt
  have hrem : SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus=a.1.val := by
    rw [hm,hword,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.1.isLt]
  have hquot : SubexponentialSAT.BinaryArithmetic.toNat
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1=a.2.val := by
    rw [SubexponentialSAT.ModularQuotientArithmetic.divide_quotient_correct modulus word (by omega),hm,hword,
      Nat.add_mul_div_left _ _ hmpos,Nat.div_eq_of_lt a.1.isLt,Nat.zero_add]
  obtain ⟨n0,hn0,r0,h0⟩ := decode_eval regs word rest width modulus
    (Encoding.encodeList id clauses) shape acc hw (by omega)
  rw [hrem] at h0
  rw [hm] at hn0
  obtain ⟨n1,hn1,r1,h1⟩ := lookup_eval r0 clauses a.1 rest width modulus shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
  have h2 := copyShape_eval r1 rest width modulus (Encoding.encodeList id clauses) shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 clauses[a.1.val]
  obtain ⟨n3,hn3,r3,h3⟩ := normalize_eval t d ht a.2 (readRegs r1 0 1 none)
    rest width modulus (Encoding.encodeList id clauses) shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 clauses[a.1.val] hshape hquot
  obtain ⟨n4,hn4,r4,h4⟩ := frameWeight_eval r3 rest width modulus
    (Encoding.encodeList id clauses) shape acc (RingProgram.flat (constantVector t d a.2)) clauses[a.1.val]
  obtain ⟨n5,hn5,r5,h5⟩ := frameRecord_eval r4 rest width modulus
    (Encoding.encodeList id clauses) shape acc (payload t d clauses a)
  have h6 := tagRecord_eval r5 rest width modulus (Encoding.encodeList id clauses) shape
    (Encoding.frame (payload t d clauses a)++acc)
  have he := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))))
  refine ⟨_,?_,_,he⟩
  have hlen := flat_length t d a.2
  rw [← hshape] at hlen
  rw [hlen] at hn4
  have hp : (payload t d clauses a).length=2*shape.length+1+clauses[a.1.val].length := by
    simp only [payload,List.length_append,Encoding.length_frame,hlen]
  rw [hp] at hn5
  rw [SubexponentialSAT.ModularQuotientArithmetic.divide_quotient_length] at hn3
  unfold termBudget
  omega

abbrev peek : Cmd 8 24 := .seq (.base (.atom (.pop 0 0 1)))
  (.ite 1 (.base (.atom (.push 0 0))) (.base .skip))

def peekRegs (regs : Fin 8 → Bool) (raw : List Bool) : Fin 8 → Bool :=
  readRegs regs 0 1 raw.head?

theorem peek_nil (regs : Fin 8 → Bool) (width modulus master shape acc : List Bool) :
    Eval peek 2 (data regs [] width modulus master shape acc [] [] [] [])
      (data (peekRegs regs []) [] width modulus master shape acc [] [] [] []) := by
  let a := data regs [] width modulus master shape acc [] [] [] []
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (0 : Fin 24) 0 1) a)
  have he : (StructuredProgram.Atom.pop (0 : Fin 24) (0 : Fin 8) 1).eval a =
      data (peekRegs regs []) [] width modulus master shape acc [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,data,tapes,
        StructuredProgram.Atom.instr,execInstr]
  rw [he] at hp
  exact hp.seq (Eval.ite_false rfl (.base (.skip _)))

theorem peek_cons (regs : Fin 8 → Bool) (bit : Bool)
    (raw width modulus master shape acc : List Bool) :
    Eval peek 3 (data regs (bit::raw) width modulus master shape acc [] [] [] [])
      (data (peekRegs regs (bit::raw)) (bit::raw) width modulus master shape acc [] [] [] []) := by
  let a := data regs (bit::raw) width modulus master shape acc [] [] [] []
  let b := (StructuredProgram.Atom.pop (0 : Fin 24) (0 : Fin 8) 1).eval a
  have hp : Eval (.base (.atom (.pop 0 0 1))) 1 a b := .base (.atom _ _)
  have hpush := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (0 : Fin 24) 0) b)
  have he : (StructuredProgram.Atom.push (0 : Fin 24) (0 : Fin 8)).eval b =
      data (peekRegs regs (bit::raw)) (bit::raw) width modulus master shape acc [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs]
  rw [he] at hpush
  exact hp.seq (Eval.ite_true rfl hpush)

abbrev loop : Cmd 8 24 := .seq peek (.while 1 (.seq term peek))

def word (b m : ℕ) (a : Fin m × ZMod 3) : List Bool :=
  SubexponentialSAT.SubexpLiftRing.fixedBits b (a.1.val+m*a.2.val)

def scanInput {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map fun a => (word b m a).reverse).flatten

def records (ps : List (List Bool)) (acc : List Bool) : List Bool :=
  ps.foldr (fun p tail => true::(Encoding.frame p++tail)) acc

@[simp] theorem records_append (xs ys : List (List Bool)) (acc : List Bool) :
    records (xs++ys) acc=records xs (records ys acc) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [records]

def loopBudget (t d b ml : ℕ) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  3+(terms.map fun a => termBudget b ml clauses.length
    (Encoding.encodeList id clauses).length ((d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    clauses[a.1.val].length+4).sum

theorem loop_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape acc : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ loopBudget t d b modulus.length clauses terms, ∃ rf,
      Eval loop n
        (data regs (scanInput b terms) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (records (terms.reverse.map (payload t d clauses)) acc) [] [] [] []) := by
  induction terms generalizing regs acc with
  | nil =>
      refine ⟨3,by simp [loopBudget],peekRegs regs [],?_⟩
      exact (peek_nil regs width modulus (Encoding.encodeList id clauses) shape acc).seq
        (Eval.while_false rfl)
  | cons a terms ih =>
      have hwlen : (word b clauses.length a).length=b := by simp [word]
      have hv : SubexponentialSAT.BinaryArithmetic.toNat (word b clauses.length a)=
          a.1.val+clauses.length*a.2.val := by
        apply SubexponentialSAT.SubexpLiftRing.toNat_fixedBits_of_lt
        have hc := a.2.val_lt
        have hi := a.1.isLt
        have : a.1.val+clauses.length*a.2.val < 3*clauses.length := by nlinarith
        exact this.trans_le hbound
      have hnonnil : (word b clauses.length a).reverse++scanInput b terms ≠ [] := by
        intro he
        have he' := congrArg List.length he
        simp [hwlen] at he'
        omega
      obtain ⟨bit,raw,hraw⟩ := List.exists_cons_of_ne_nil hnonnil
      have hp := peek_cons regs bit raw width modulus (Encoding.encodeList id clauses) shape acc
      rw [← hraw] at hp
      obtain ⟨nu,hnu,ru,hu⟩ := term_eval t d ht clauses a
        (peekRegs regs ((word b clauses.length a).reverse++scanInput b terms))
        (word b clauses.length a) (scanInput b terms) width modulus shape acc
        (hw.trans hwlen.symm) hm hshape hv
      obtain ⟨nv,hnv,rv,hv⟩ := ih ru (true::(Encoding.frame (payload t d clauses a)++acc))
      cases hv with
      | @seq first second nx ny aa bb cc hpeek hwhile =>
          have hg : (data (peekRegs regs ((word b clauses.length a).reverse++scanInput b terms))
              ((word b clauses.length a).reverse++scanInput b terms) width modulus
              (Encoding.encodeList id clauses) shape acc [] [] [] []).regs 1=true := by
            rw [hraw]
            rfl
          have he := hp.seq (Eval.while_true hg (hu.seq hpeek) hwhile)
          refine ⟨3+(nu+nx+ny+1),?_,rv,?_⟩
          · rw [hwlen,hshape] at hnu
            simp only [loopBudget,List.map_cons,List.sum_cons] at *
            omega
          · simpa [scanInput,List.reverse_cons,List.map_append,records_append,records] using he

def program := compiled loop 0 16

theorem program_runs (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (loopBudget t d b modulus.length clauses terms+1)
      ((data regs (scanInput b terms) width modulus (Encoding.encodeList id clauses)
        shape [false] [] [] [] []).withPC (some program.entry))
      ((data rf [] width modulus (Encoding.encodeList id clauses) shape
        (Encoding.encodeList id (terms.reverse.map (payload t d clauses))) [] [] [] []).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := loop_eval t d ht b hb clauses terms hbound regs width modulus shape [false]
    hw hm hshape
  have hh (ps : List (List Bool)) : records ps [false]=Encoding.encodeList id ps := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
        change true::(Encoding.frame p++records ps [false]) =
          true::(Encoding.frame p++Encoding.encodeList id ps)
        rw [ih]
  rw [hh] at he
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 0 16⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
