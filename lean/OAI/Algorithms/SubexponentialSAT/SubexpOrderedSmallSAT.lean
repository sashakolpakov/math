import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FinitePrefixProgram
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawPrefix

namespace OAI.Algorithms

/-!
# A physical small-variable SAT fallback for ordered input lists

For a fixed variable cutoff, a finite control state records the truth values
of the current clause and completed formula on every cutoff-sized assignment.
The scanner parses the two fixed framing levels and unary literal codes.
It accepts arbitrary clause/literal order and repetitions, rather than a
finite collection of canonical input words. The compiled scanner consumes
three instructions per input bit and six instructions to return its answer.
-/

namespace SubexponentialSAT.SubexpOrderedSmallSAT

open BitProgram
open SubexpOrderedRawPrefix (Formula encode bitLength)

abbrev Assignment (N : ℕ) := Fin N → Bool
abbrev Mask (N : ℕ) := Assignment N → Bool

def zeroMask (N : ℕ) : Mask N := fun _ => false
def oneMask (N : ℕ) : Mask N := fun _ => true
def orMask {N : ℕ} (a b : Mask N) : Mask N := fun x => a x || b x
def andMask {N : ℕ} (a b : Mask N) : Mask N := fun x => a x && b x

@[simp] theorem zero_or {N : ℕ} (a : Mask N) : orMask (zeroMask N) a = a := by
  funext x; simp [orMask,zeroMask]
@[simp] theorem or_zero {N : ℕ} (a : Mask N) : orMask a (zeroMask N) = a := by
  funext x; simp [orMask,zeroMask]
@[simp] theorem one_and {N : ℕ} (a : Mask N) : andMask (oneMask N) a = a := by
  funext x; simp [andMask,oneMask]
@[simp] theorem and_one {N : ℕ} (a : Mask N) : andMask a (oneMask N) = a := by
  funext x; simp [andMask,oneMask]
theorem or_assoc {N : ℕ} (a b c : Mask N) :
    orMask (orMask a b) c = orMask a (orMask b c) := by
  funext x; exact Bool.or_assoc _ _ _
theorem and_assoc {N : ℕ} (a b c : Mask N) :
    andMask (andMask a b) c = andMask a (andMask b c) := by
  funext x; exact Bool.and_assoc _ _ _

/-- The counter is part of a finite control state, with an explicit overflow cap. -/
def cap (N k : ℕ) : Fin (2*N+1) := ⟨min k (2*N),Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

@[simp] theorem cap_val {N k : ℕ} (h : k ≤ 2*N) : (cap N k).val = k :=
  Nat.min_eq_left h

def increment {N : ℕ} (c : Fin (2*N+1)) : Fin (2*N+1) := cap N (c.val+1)

theorem increment_cap (N k : ℕ) (h : k ≤ 2*N) :
    increment (cap N k) = cap N (k+1) := by simp [increment,cap_val h]

/-- This finite truth table is compiled into the scanner's control table. -/
def literalMask (N : ℕ) (c : Fin (2*N+1)) : Mask N := fun a =>
  decide (∃ l : SAT.Literal (Fin N), Encoding.literalCode l = c.val ∧ l.eval a = true)

inductive Inner (N : ℕ) where
  | tag (hit : Mask N)
  | frame (code : Fin (2*N+1)) (hit : Mask N)
  | value (code : Fin (2*N+1)) (hit : Mask N)
  deriving Fintype

def Inner.hit {N : ℕ} : Inner N → Mask N
  | .tag h => h
  | .frame _ h => h
  | .value _ h => h

def innerNext {N : ℕ} : Inner N → Bool → Inner N
  | .tag hit, false => .tag hit
  | .tag hit, true => .frame (cap N 0) hit
  | .frame code hit, false => .tag (orMask hit (literalMask N code))
  | .frame code hit, true => .value code hit
  | .value code hit, false => .frame code hit
  | .value code hit, true => .frame (increment code) hit

def innerEval {N : ℕ} (q : Inner N) (bits : List Bool) : Inner N := bits.foldl innerNext q

theorem innerEval_append {N : ℕ} (q : Inner N) (a b : List Bool) :
    innerEval q (a++b) = innerEval (innerEval q a) b := by
  simp only [innerEval,List.foldl_append]

theorem inner_number (N k m : ℕ) (hit : Mask N) (h : k+m ≤ 2*N) :
    innerEval (.frame (cap N k) hit) (Encoding.frame (Encoding.encodeNat m)) =
      .tag (orMask hit (literalMask N (cap N (k+m)))) := by
  induction m generalizing k with
  | zero => simp [innerEval,Encoding.encodeNat,Encoding.frame,innerNext]
  | succ m ih =>
      have hk : k ≤ 2*N := by omega
      have hm : (k+1)+m ≤ 2*N := by omega
      have hin : Encoding.encodeNat (m+1) = true :: Encoding.encodeNat m := by
        simp [Encoding.encodeNat,List.replicate_succ]
      rw [hin]
      rw [Encoding.frame_cons]
      simp only [innerEval, List.foldl_cons, innerNext, increment_cap N k hk]
      change innerEval (.frame (cap N (k+1)) hit) (Encoding.frame (Encoding.encodeNat m)) = _
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) hm

def clauseMask (N : ℕ) : List ℕ → Mask N
  | [] => zeroMask N
  | k::ks => orMask (literalMask N (cap N k)) (clauseMask N ks)

theorem inner_clause (N : ℕ) (codes : List ℕ) (hit : Mask N)
    (hcodes : ∀ k ∈ codes, k ≤ 2*N) :
    innerEval (.tag hit) (Encoding.encodeList Encoding.encodeNat codes) =
      .tag (orMask hit (clauseMask N codes)) := by
  induction codes generalizing hit with
  | nil => simp [innerEval,Encoding.encodeList,innerNext,clauseMask]
  | cons k ks ih =>
      have hk := hcodes k (by simp)
      have hs : ∀ j ∈ ks, j ≤ 2*N := fun j hj => hcodes j (by simp [hj])
      simp only [Encoding.encodeList,innerEval,List.foldl_cons,innerNext,List.foldl_append]
      change innerEval (innerEval (.frame (cap N 0) hit)
        (Encoding.frame (Encoding.encodeNat k))) (Encoding.encodeList Encoding.encodeNat ks) = _
      rw [inner_number N 0 k hit (by simpa using hk),Nat.zero_add]
      rw [ih _ hs]
      simp only [clauseMask,or_assoc]

inductive State (N : ℕ) where
  | header
  | formula (good : Mask N)
  | frame (good : Mask N) (inner : Inner N)
  | data (good : Mask N) (inner : Inner N)
  | done (good : Mask N)
  deriving Fintype

def next {N : ℕ} : State N → Bool → State N
  | .header, true => .header
  | .header, false => .formula (oneMask N)
  | .formula good, true => .frame good (.tag (zeroMask N))
  | .formula good, false => .done good
  | .frame good inner, true => .data good inner
  | .frame good inner, false => .formula (andMask good inner.hit)
  | .data good inner, bit => .frame good (innerNext inner bit)
  | .done good, _ => .done good

def eval {N : ℕ} (q : State N) (bits : List Bool) : State N := bits.foldl next q

theorem eval_append {N : ℕ} (q : State N) (a b : List Bool) :
    eval q (a++b) = eval (eval q a) b := by
  simp only [eval,List.foldl_append]

theorem eval_header (N n : ℕ) : eval (State.header (N := N)) (Encoding.encodeNat n) =
    .formula (oneMask N) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hin : Encoding.encodeNat (n+1) = true :: Encoding.encodeNat n := by
        simp [Encoding.encodeNat,List.replicate_succ]
      simpa only [hin,eval,List.foldl_cons,next] using ih

theorem eval_frame {N : ℕ} (good : Mask N) (inner : Inner N) (bits : List Bool) :
    eval (.frame good inner) (Encoding.frame bits) =
      .formula (andMask good (innerEval inner bits).hit) := by
  induction bits generalizing inner with
  | nil => rfl
  | cons b bs ih =>
      rw [Encoding.frame_cons]
      simp only [eval, innerEval, List.foldl_cons, next]
      exact ih (innerNext inner b)

def formulaMask (N : ℕ) : List (List ℕ) → Mask N
  | [] => oneMask N
  | c::cs => andMask (clauseMask N c) (formulaMask N cs)

theorem eval_formula (N : ℕ) (codes : List (List ℕ)) (good : Mask N)
    (hcodes : ∀ c ∈ codes, ∀ k ∈ c, k ≤ 2*N) :
    eval (.formula good) (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) codes) =
      .done (andMask good (formulaMask N codes)) := by
  induction codes generalizing good with
  | nil => simp [eval,Encoding.encodeList,next,formulaMask]
  | cons c cs ih =>
      have hc : ∀ k ∈ c, k ≤ 2*N := hcodes c (by simp)
      have hs : ∀ d ∈ cs, ∀ k ∈ d, k ≤ 2*N := fun d hd => hcodes d (by simp [hd])
      simp only [Encoding.encodeList,eval,List.foldl_cons,next,List.foldl_append]
      change eval (eval (.frame good (.tag (zeroMask N)))
        (Encoding.frame (Encoding.encodeList Encoding.encodeNat c)))
          (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) cs) = _
      rw [eval_frame,inner_clause N c (zeroMask N) hc,Inner.hit,zero_or,ih _ hs]
      simp only [formulaMask,and_assoc]

def accept {N : ℕ} : State N → Bool
  | .done good => decide (∃ a : Assignment N, good a = true)
  | _ => false

def restrict {N n : ℕ} (h : n ≤ N) (a : Assignment N) : SAT.Assignment (Fin n) :=
  fun i => a (Fin.castLE h i)

def liftLiteral {N n : ℕ} (h : n ≤ N) (l : SAT.Literal (Fin n)) : SAT.Literal (Fin N) :=
  ⟨Fin.castLE h l.variable,l.positive⟩

@[simp] theorem liftLiteral_code {N n : ℕ} (h : n ≤ N) (l : SAT.Literal (Fin n)) :
    Encoding.literalCode (liftLiteral h l) = Encoding.literalCode l := rfl

@[simp] theorem liftLiteral_eval {N n : ℕ} (h : n ≤ N) (l : SAT.Literal (Fin n))
    (a : Assignment N) : (liftLiteral h l).eval a = l.eval (restrict h a) := rfl

theorem literalMask_code {N n : ℕ} (h : n ≤ N) (l : SAT.Literal (Fin n))
    (a : Assignment N) :
    literalMask N (cap N (Encoding.literalCode l)) a = l.eval (restrict h a) := by
  have hc : Encoding.literalCode l ≤ 2*N := by
    have hl := Encoding.literalCode_lt l
    omega
  apply Bool.eq_iff_iff.mpr
  simp only [literalMask,decide_eq_true_eq,cap_val hc]
  rw [← liftLiteral_code h l]
  simp only [Encoding.literalCode_injective.eq_iff,exists_eq_left,liftLiteral_eval]

def clauseValue {n : ℕ} (a : SAT.Assignment (Fin n)) (C : List (SAT.Literal (Fin n))) : Bool :=
  C.any (fun l => l.eval a)

def formulaValue {n : ℕ} (a : SAT.Assignment (Fin n)) (G : Formula n) : Bool :=
  G.all (clauseValue a)

theorem clauseMask_codes {N n : ℕ} (h : n ≤ N) (C : List (SAT.Literal (Fin n)))
    (a : Assignment N) :
    clauseMask N (C.map Encoding.literalCode) a = clauseValue (restrict h a) C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [List.map_cons,clauseMask,orMask,clauseValue,List.any_cons,
        literalMask_code h l a]
      exact congrArg (fun b => l.eval (restrict h a) || b) ih

theorem formulaMask_codes {N n : ℕ} (h : n ≤ N) (G : Formula n) (a : Assignment N) :
    formulaMask N (G.map (List.map Encoding.literalCode)) a = formulaValue (restrict h a) G := by
  induction G with
  | nil => rfl
  | cons C G ih =>
      simp only [List.map_cons,formulaMask,andMask,formulaValue,List.all_cons,
        clauseMask_codes h C a]
      exact congrArg (fun b => clauseValue (restrict h a) C && b) ih

theorem formulaValue_correct {n : ℕ} (a : SAT.Assignment (Fin n)) (G : Formula n) :
    formulaValue a G = true ↔ SAT.CNF.eval a (ExecCNF.formulaSet G) = true := by
  simp only [formulaValue,List.all_eq_true,clauseValue,List.any_eq_true,
    SAT.CNF.eval_eq_true,SAT.Clause.eval_eq_true,ExecCNF.mem_formulaSet]
  constructor
  · intro h C hC
    obtain ⟨D,hD,rfl⟩ := hC
    simpa only [ExecCNF.mem_clauseSet] using h D hD
  · intro h C hC
    simpa only [ExecCNF.mem_clauseSet] using h (ExecCNF.clauseSet C) ⟨C,hC,rfl⟩

def extend {N n : ℕ} (a : SAT.Assignment (Fin n)) : Assignment N := fun i =>
  if h : i.val < n then a ⟨i.val,h⟩ else false

theorem restrict_extend {N n : ℕ} (h : n ≤ N) (a : SAT.Assignment (Fin n)) :
    restrict h (extend (N := N) a) = a := by
  funext i
  simp [restrict,extend,i.isLt]

theorem exists_formulaValue {N n : ℕ} (h : n ≤ N) (G : Formula n) :
    (∃ a : Assignment N, formulaValue (restrict h a) G = true) ↔
      SAT.Satisfiable (ExecCNF.formulaSet G) := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨restrict h a,(formulaValue_correct _ _).mp ha⟩
  · rintro ⟨a,ha⟩
    refine ⟨extend a,?_⟩
    rw [restrict_extend h]
    exact (formulaValue_correct _ _).mpr ha

theorem eval_encode {N n : ℕ} (G : Formula n) (h : n ≤ N) :
    eval (State.header (N := N)) (encode G) =
      .done (formulaMask N (G.map (List.map Encoding.literalCode))) := by
  have hcodes : ∀ c ∈ G.map (List.map Encoding.literalCode), ∀ k ∈ c, k ≤ 2*N := by
    intro c hc k hk
    obtain ⟨C,_,rfl⟩ := List.mem_map.mp hc
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hk
    have hb := Encoding.literalCode_lt l
    omega
  rw [SubexpOrderedRawPrefix.encode_eq,eval_append,eval_header,
    eval_formula N _ (oneMask N) hcodes,one_and]

theorem accept_encode {N n : ℕ} (G : Formula n) (h : n ≤ N) :
    accept (eval (State.header (N := N)) (encode G)) = true ↔
      SAT.Satisfiable (ExecCNF.formulaSet G) := by
  rw [eval_encode G h]
  simp only [accept,decide_eq_true_eq,formulaMask_codes h]
  exact exists_formulaValue h G

/-- Only the fixed cutoff selects this finite transition table. -/
noncomputable def scanner (N : ℕ) : FixedParameters.Scanner :=
  FixedParameters.scannerOfFinite (State.header (N := N)) next accept

theorem scanner_correct (N n : ℕ) (G : Formula n) (h : n ≤ N) :
    (scanner N).accept (FixedParameters.scannerEval (scanner N) (scanner N).start (encode G)) =
        true ↔ SAT.Satisfiable (ExecCNF.formulaSet G) := by
  unfold scanner
  rw [show (FixedParameters.scannerOfFinite (State.header (N := N)) next accept).start =
    Fintype.equivFin (State N) .header from rfl]
  rw [FixedParameters.scannerOfFinite_eval]
  simpa only [FixedParameters.scannerOfFinite,Equiv.symm_apply_apply,eval] using accept_encode G h

/-- A physical two-register program accepting all bounded-variable ordered encodings. -/
noncomputable def smallProgram {s : ℕ} (N : ℕ) (input output : Fin s) :=
  FinitePrefixProgram.Language.program (scanner N) input output

theorem small_trace {s : ℕ} (N n : ℕ) (G : Formula n) (hn : n < N)
    (input output : Fin s) :
    ∃ answer, Trace (smallProgram N input output) (3*bitLength G+6)
      (initial (smallProgram N input output) (encode G))
      (terminal (smallProgram N input output) [answer]) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) := by
  refine ⟨(scanner N).accept
    (FixedParameters.scannerEval (scanner N) (scanner N).start (encode G)),?_,
    scanner_correct N n G hn.le⟩
  exact FinitePrefixProgram.Language.initial_trace (scanner N) input output (encode G)

theorem small_runsIn {s : ℕ} (N n : ℕ) (G : Formula n) (hn : n < N)
    (input output : Fin s) :
    ∃ answer, RunsIn (smallProgram N input output) (3*bitLength G+6)
      (initial (smallProgram N input output) (encode G))
      (terminal (smallProgram N input output) [answer]) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) := by
  obtain ⟨answer,ht,ha⟩ := small_trace N n G hn input output
  exact ⟨answer,⟨_,le_rfl,ht⟩,ha⟩

theorem small_primitive {s : ℕ} (N n : ℕ) (G : Formula n) (hn : n < N)
    (input output : Fin s) :
    ∃ answer, (primitive (smallProgram N input output)).OutputsInTime (encode G) answer
      (primitiveOverhead (smallProgram N input output)*(3*bitLength G+6)) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) := by
  obtain ⟨answer,ht,ha⟩ := small_runsIn N n G hn input output
  refine ⟨answer,primitive_outputs_of_halted _ ht rfl ?_,ha⟩
  simp []

end SubexponentialSAT.SubexpOrderedSmallSAT

end OAI.Algorithms
