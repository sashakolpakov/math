import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

/-- A concrete entry command, with explicit execution and frame obligations.
No list of entries is an input to the fiber machine. -/
def EntryAt (entry : Code) (base : Data) (value : ℕ → ℤ) (T B M i : ℕ) : Prop :=
  ∀ (regs : Fin 16 → Bool) (queue : List Bool) (acc : WordPair),
    ∃ n ≤ T, ∃ rf result,
      Eval entry n (data base regs queue (unary i) acc ([],[]))
        (data base rf queue (unary i) acc result) ∧
      pairValue result=value i ∧ pairLength result ≤ B ∧ pairTotal result.1 result.2 ≤ M

def body (entry : Code) : Code := .seq readIndex (.seq entry (.seq addEntry clearColumn))
def bodyBudget (T B i L : ℕ) : ℕ := T+5*i+8+25000*(L+B+3)^2

theorem body_eval (entry : Code) (base : Data) (hb : ArithmeticReady base)
    (value : ℕ → ℤ) (T B M i L : ℕ) (hentry : EntryAt entry base value T B M i)
    (regs : Fin 16 → Bool) (queue : List Bool) (acc : WordPair) (hL : pairLength acc ≤ L) :
    ∃ n ≤ bodyBudget T B i L, ∃ rf result,
      Eval (body entry) n (data base regs (Encoding.encodeNat i++queue) [] acc ([],[]))
        (data base rf queue [] result ([],[])) ∧
      pairValue result=pairValue acc+value i ∧
      pairLength result ≤ L+B+2 ∧
      pairTotal result.1 result.2 ≤ pairTotal acc.1 acc.2+M := by
  have hr := readIndex_eval base regs i queue acc
  obtain ⟨ne,hne,re,next,he,hv,hl,hm⟩ :=
    hentry (readRegs regs 0 1 (some false)) queue acc
  obtain ⟨na,hna,ra,result,ha,hav,ham,hal⟩ :=
    addEntry_eval base hb re queue (unary i) acc next
  have hc := clearColumn_eval base ra queue (unary i) result
  have hh := hr.seq (he.seq (ha.seq hc))
  refine ⟨_,?_,readRegs ra 0 1 none,result,hh,?_,?_,?_⟩
  · have hs : (pairLength acc+pairLength next+3)^2 ≤ (L+B+3)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    simp only [unary,List.length_replicate] at hh ⊢
    unfold bodyBudget
    omega
  · simpa only [hv] using hav
  · omega
  · omega

def peek : Code := .seq (.base (.atom (.pop 214 14 15)))
  (.ite 15 (.base (.atom (.push 214 14))) (.base .skip))
def peekRegs (regs : Fin 16 → Bool) (queue : List Bool) : Fin 16 → Bool :=
  readRegs regs 14 15 queue.head?

theorem peek_nil (base : Data) (regs : Fin 16 → Bool) (acc : WordPair) :
    Eval peek 2 (data base regs [] [] acc ([],[]))
      (data base (peekRegs regs []) [] [] acc ([],[])) := by
  let a := data base regs [] [] acc ([],[])
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (214 : Fin 256) 14 15) a)
  have he : (StructuredProgram.Atom.pop (214 : Fin 256) (14 : Fin 16) 15).eval a=
      data base (peekRegs regs []) [] [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i=214
      · subst i; simp [a,data,bank,StructuredProgram.Atom.instr,execInstr]
      simp [a,data,bank,StructuredProgram.Atom.instr,execInstr,hi]
  rw [he] at hp
  exact hp.seq (Eval.ite_false rfl (.base (.skip _)))

theorem peek_cons (base : Data) (regs : Fin 16 → Bool) (bit : Bool)
    (queue : List Bool) (acc : WordPair) :
    Eval peek 3 (data base regs (bit::queue) [] acc ([],[]))
      (data base (peekRegs regs (bit::queue)) (bit::queue) [] acc ([],[])) := by
  let a := data base regs (bit::queue) [] acc ([],[])
  let b := (StructuredProgram.Atom.pop (214 : Fin 256) (14 : Fin 16) 15).eval a
  have hp : Eval (.base (.atom (.pop 214 14 15))) 1 a b := .base (.atom _ _)
  have hpush := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (214 : Fin 256) 14) b)
  have he : (StructuredProgram.Atom.push (214 : Fin 256) (14 : Fin 16)).eval b=
      data base (peekRegs regs (bit::queue)) (bit::queue) [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i=214
      · subst i; simp [a,b,data,bank,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,readRegs]
      simp [a,b,data,bank,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,readRegs,hi]
  rw [he] at hpush
  exact hp.seq (Eval.ite_true rfl hpush)

def loop (entry : Code) : Code := .seq peek (.while 15 (.seq (body entry) peek))
def cost (T B : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 3
  | i::is, L => bodyBudget T B i L+cost T B is (L+B+2)+4

theorem loop_eval (entry : Code) (base : Data) (hb : ArithmeticReady base)
    (value : ℕ → ℤ) (T B M : ℕ) (is : List ℕ)
    (hentry : ∀ i∈is, EntryAt entry base value T B M i)
    (regs : Fin 16 → Bool) (acc : WordPair) (L : ℕ) (hL : pairLength acc ≤ L) :
    ∃ n ≤ cost T B is L, ∃ rf result,
      Eval (loop entry) n (data base regs (encodeIndices is) [] acc ([],[]))
        (data base rf [] [] result ([],[])) ∧
      pairValue result=pairValue acc+(is.map value).sum ∧
      pairLength result ≤ L+is.length*(B+2) ∧
      pairTotal result.1 result.2 ≤ pairTotal acc.1 acc.2+is.length*M := by
  induction is generalizing regs acc L with
  | nil =>
      refine ⟨3,by simp [cost],peekRegs regs [],acc,?_,?_,?_,?_⟩
      · exact (peek_nil base regs acc).seq (Eval.while_false rfl)
      · simp
      · simpa using hL
      · simp
  | cons i is ih =>
      have hnonnil : Encoding.encodeNat i++encodeIndices is ≠ [] := by
        simp [Encoding.encodeNat]
      obtain ⟨bit,tail,htail⟩ := List.exists_cons_of_ne_nil hnonnil
      have hp := peek_cons base regs bit tail acc
      rw [←htail] at hp
      obtain ⟨nt,hnt,rt,next,het,hvt,hlt,hmt⟩ := body_eval entry base hb value T B M i L
        (hentry i (by simp)) (peekRegs regs (Encoding.encodeNat i++encodeIndices is))
        (encodeIndices is) acc hL
      obtain ⟨nr,hnr,rf,result,her,hvr,hlr,hmr⟩ := ih
        (fun j hj => hentry j (by simp [hj])) rt next (L+B+2) hlt
      cases her with
      | @seq first second nx ny aa bb cc hpeek hwhile =>
          have hg : (data base (peekRegs regs (Encoding.encodeNat i++encodeIndices is))
              (Encoding.encodeNat i++encodeIndices is) [] acc ([],[])).regs 15=true := by
            rw [htail]
            rfl
          have hh := hp.seq (Eval.while_true hg (het.seq hpeek) hwhile)
          refine ⟨3+(nt+nx+ny+1),?_,rf,result,?_,?_,?_,?_⟩
          · simp only [cost]
            omega
          · simpa only [loop, encodeIndices, List.flatMap_cons] using hh
          · rw [hvr,hvt]
            simp [add_assoc]
          · simp only [List.length_cons]
            nlinarith
          · simp only [List.length_cons]
            nlinarith

theorem cost_le (T B J L : ℕ) (is : List ℕ) (hJ : ∀ i∈is, i ≤ J) :
    cost T B is L ≤ 3+is.length*(T+5*J+12+
      25000*(L+(is.length+1)*(B+2)+3)^2) := by
  induction is generalizing L with
  | nil => simp [cost]
  | cons i is ih =>
      have hi := hJ i (by simp)
      have ht := ih (L+B+2) (fun j hj => hJ j (by simp [hj]))
      have heq : L+B+2+(is.length+1)*(B+2)+3 =
          L+(is.length+1+1)*(B+2)+3 := by ring
      rw [heq] at ht
      have hs : (L+B+3)^2 ≤ (L+(is.length+1+1)*(B+2)+3)^2 :=
        Nat.pow_le_pow_left (by nlinarith) 2
      simp only [cost,bodyBudget,List.length_cons]
      nlinarith

def program (entry : Code) := compiled (loop entry) 214 212

theorem program_runs (entry : Code) (base : Data) (hb : ArithmeticReady base)
    (value : ℕ → ℤ) (T B M J : ℕ) (is : List ℕ)
    (hentry : ∀ i∈is, EntryAt entry base value T B M i)
    (hJ : ∀ i∈is, i ≤ J) (regs : Fin 16 → Bool) :
    ∃ rf result, RunsIn (program entry)
      (4+is.length*(T+5*J+12+25000*((is.length+1)*(B+2)+3)^2))
      ((data base regs (encodeIndices is) [] ([],[]) ([],[])).withPC (some (program entry).entry))
      ((data base rf [] [] result ([],[])).withPC none) ∧
      pairValue result=(is.map value).sum ∧
      pairLength result ≤ is.length*(B+2) ∧
      pairTotal result.1 result.2 ≤ is.length*M := by
  obtain ⟨n,hn,rf,result,he,hv,hl,hm⟩ :=
    loop_eval entry base hb value T B M is hentry regs ([],[]) 0 (by simp [pairLength])
  have hc := cost_le T B J 0 is hJ
  refine ⟨rf,result,⟨n+1,?_,compiled_halt_trace he 214 212⟩,?_,?_,?_⟩
  · simp only [Nat.zero_add] at hc
    omega
  · simpa [pairValue,signedValue] using hv
  · simpa using hl
  · simpa [pairTotal] using hm

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
