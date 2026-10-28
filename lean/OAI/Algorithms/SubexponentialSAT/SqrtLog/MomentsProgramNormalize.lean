import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramRead

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

def denoteTable (f : C → R) (entries : List (K × C)) : Squarefree.Sparse.Data K R :=
  entries.map fun a => (a.1,f a.2)

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_cons (f : C → R) (a : K × C) (entries : List (K × C)) :
    denoteTable f (a::entries) = (a.1,f a.2)::denoteTable f entries := rfl

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_reverse (f : C → R) (entries : List (K × C)) :
    denoteTable f entries.reverse = (denoteTable f entries).reverse := by
  simp [denoteTable]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

omit [CommRing R] in
theorem denoteTable_lookup (f : C → R) (entries : List (K × C)) (k : K) :
    (denoteTable f entries).lookup k = (entries.lookup k).map f := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j; simp [denoteTable]
    · simp only [denoteTable,List.map_cons,List.lookup_cons] at ih ⊢
      simp [beq_false_of_ne (Ne.symm h),ih]

omit [CommRing R] in
theorem denoteTable_erase (f : C → R) (entries : List (K × C)) (k : K) :
    denoteTable f (Squarefree.Sparse.erase k entries) =
      Squarefree.Sparse.erase k (denoteTable f entries) := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    by_cases h : a.1=k <;> simp [denoteTable,Squarefree.Sparse.erase,h] at ih ⊢ <;> exact ih

theorem denoteTable_insertCode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    denoteTable f (insertCode p t M cache k x entries) =
      Squarefree.Program.put k (f x + Squarefree.Sparse.fetch k (denoteTable f entries)) (denoteTable f entries) := by
  dsimp only
  let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
  have hf := Squarefree.Program.fetch_eq_lookup (denoteTable f entries) k
    (by simpa only [denoteTable_keys] using hn)
  rw [denoteTable_lookup] at hf
  have ha (y : RingProgram.Code (Word (baseWidth p t)) d) :
      f (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1 = f x + f y :=
    RingProgram.denote_add (RingProgram.scalarRing p t M cache) scalar basis x y
  change denoteTable f _ = Squarefree.Program.put k
    (f x + Squarefree.Sparse.fetch k (denoteTable f entries)) (denoteTable f entries)
  cases he : entries.lookup k
  · have hz : Squarefree.Sparse.fetch k (denoteTable f entries) = 0 := by simpa [he] using hf
    simp only [insertCode,he,denoteTable_cons,denoteTable_reverse,Squarefree.Program.put]
    change (k,f x)::(denoteTable f (Squarefree.Sparse.erase k entries)).reverse =
      (k,f x + Squarefree.Sparse.fetch k (denoteTable f entries))::
        (Squarefree.Sparse.erase k (denoteTable f entries)).reverse
    rw [hz,add_zero,denoteTable_erase]
  · rename_i y
    have hy : Squarefree.Sparse.fetch k (denoteTable f entries) = f y := by simpa [he] using hf
    simp only [insertCode,he,denoteTable_cons,denoteTable_reverse,Squarefree.Program.put]
    change (k,f (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)::
        (denoteTable f (Squarefree.Sparse.erase k entries)).reverse =
      (k,f x + Squarefree.Sparse.fetch k (denoteTable f entries))::
        (Squarefree.Sparse.erase k (denoteTable f entries)).reverse
    rw [ha,hy,denoteTable_erase]

/-- Actual code insertion preserves sparse polynomial addition semantics. -/
theorem insertCode_decode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R) (atom : K → R → A)
    (hz : ∀ k, atom k 0 = 0) (ha : ∀ k x y, atom k (x+y) = atom k x + atom k y)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.decode atom (denoteTable f (insertCode p t M cache k x entries)) =
      atom k (f x) + Squarefree.Sparse.decode atom (denoteTable f entries) := by
  dsimp only
  rw [denoteTable_insertCode p t M cache scalar basis entries k x hn,
    Squarefree.Program.decode_put_add,Squarefree.Sparse.decode_insert atom hz ha]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

 theorem rawEntries_length_le (entries : List (List Bool × List Bool)) (W C : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C) :
    (Squarefree.Program.rawEntries entries).length ≤ entries.length * (2*W+2*C+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.rawEntries]
  | cons a entries ih =>
    have h1 := hk a (by simp)
    have h2 := hc a (by simp)
    have h3 := ih (fun b hb => hk b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
    simp only [Squarefree.Program.rawEntries,List.length_append,Encoding.length_frame,List.length_cons]
    nlinarith

theorem updatedBytes_length_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    (updatedBytes entries query coeff).length ≤ (entries.length+1)*(2*W+2*C+2) := by
  have hn : (((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse)).length ≤ entries.length+1 := by
    simpa [Squarefree.Program.erasedEntries] using Nat.add_le_add_right
      (List.length_filter_le (fun a : List Bool × List Bool => decide (a.1 ≠ query)) entries) 1
  have hb := rawEntries_length_le ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse) W C
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hq
        exact hk a (List.mem_filter.mp ha).1)
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hv
        exact hc a (List.mem_filter.mp ha).1)
  exact hb.trans (Nat.mul_le_mul_right _ hn)

/-- Total insertion work includes both full table scans, copied table bytes,
coefficient addition, and final replacement serialization. -/
theorem insertBudget_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (branch W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    insertBudget entries query coeff branch ≤ 200*(entries.length+1)*(W+C+1)+branch := by
  have hr := rawEntries_length_le entries W C hk hc
  have hu := updatedBytes_length_le entries query coeff W C hk hc hq hv
  have hl := Squarefree.Program.lookupBudget_bound query entries W C hk hc
  have he := Squarefree.Program.eraseBudget_bound query entries W C hk hc
  unfold insertBudget finishBudget
  nlinarith [Nat.mul_le_mul_left entries.length hq]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 28

def lower : Fin 27 → Fin 28 := Fin.castSucc

def extend (d : Dictionary.Data) (source : List Bool) : Data :=
  ⟨d.regs,Fin.snoc d.stacks source⟩

theorem lower_injective : Function.Injective lower := Fin.castSucc_injective _

theorem embed_lower (a b : Dictionary.Data) (source : List Bool) :
    embedState id lower (extend a source) b = extend b source := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lower_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; simp [extend,lower]
  · intro i hi
    fin_cases i <;> simp_all [lower,extend,Fin.exists_fin_succ,Fin.snoc]

abbrev insert : Cmd 8 28 := .call (ProgramLinking.liftProgram Dictionary.insertProgram id lower)
abbrev clearCoefficient : Cmd 8 28 := .call (StackRoutines.clearProgram 17 0 1)
abbrev peek : Cmd 8 28 := .base (.atom (.peek 27 0 7))

def peeked (d : Data) : Data :=
  ⟨readRegs d.regs 0 7 (d.stacks 27).head?,d.stacks⟩

theorem peek_eval (d : Data) : Eval peek 1 d (peeked d) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem insert_eval {n : ℕ} {a b : Dictionary.Data}
    (he : Eval Dictionary.insert n a b) (source : List Bool) :
    Eval insert (n+1) (extend a source) (extend b source) := by
  have h := eval_call_lifted Dictionary.insertProgram id lower (extend a source)
    Function.injective_id lower_injective (compiled_halt_trace he 15 15)
  simpa only [embed_lower] using h

variable {K : Type*} [DecidableEq K]

/-- Streaming order agrees semantically with normalized sparse addition;
the fixed physical loop will realize this tail-recursive traversal. -/
def run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} :
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d)
  | [], seed => seed
  | a::source, seed => run p t M cache source (Dictionary.insertCode p t M cache a.1 a.2 seed)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

 def state (regs : Fin 8 → Bool) (modulus width count dict source : List Bool) : Data :=
  extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict [])) source

abbrev step : Cmd 8 28 := .seq Squarefree.Program.takeDictionaryRecord (.seq insert clearCoefficient)

theorem read_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (key coeff tail : List Bool) :
    Eval Squarefree.Program.takeDictionaryRecord (6*key.length+9*coeff.length+11)
      (state regs modulus width count (Squarefree.Program.rawEntries entries)
        (Encoding.frame key ++ Encoding.frame coeff ++ tail))
      (extend (Dictionary.machine (readRegs regs 0 1 none)
        (Dictionary.inputTape modulus width count entries key coeff)) tail) := by
  have h := Squarefree.Program.takeDictionaryRecord_eval
    (state regs modulus width count (Squarefree.Program.rawEntries entries)
      (Encoding.frame key ++ Encoding.frame coeff ++ tail)) key coeff tail rfl rfl rfl rfl
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [state,extend,
      Dictionary.machine,Dictionary.inputTape,Dictionary.outputTape,Dictionary.tapes,Fin.snoc]
    all_goals rfl

theorem clearCoefficient_eval (regs : Fin 8 → Bool)
    (modulus width count dict coeff tail : List Bool) :
    Eval clearCoefficient (2*coeff.length+3)
      (extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict coeff)) tail)
      (state (readRegs regs 0 1 none) modulus width count dict tail) := by
  let d := extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict coeff)) tail
  let next : Data := ⟨readRegs d.regs 0 1 none,clearStacks 17 d.stacks⟩
  have h := clearProgram_trace (17 : Fin 28) (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  have hlen : d.stacks 17 = coeff := rfl
  have hrun : Eval clearCoefficient (2*coeff.length+3) d next := by
    apply Eval.call
    simpa only [clearResult,StructuredProgram.State.withPC,next,hlen,Nat.add_assoc] using hh
  have hs : next = state (readRegs regs 0 1 none) modulus width count dict tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [clearStacks,d,extend,
        Dictionary.machine,Dictionary.outputTape,Dictionary.tapes,Fin.snoc]
      all_goals first | rfl
  rwa [hs] at hrun

variable {K : Type*} [DecidableEq K]

def stepBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d) : ℕ :=
  let value := match seed.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  6*(key k).length + 11*(RingProgram.flat x).length + 15 +
    Dictionary.insertBudget (Squarefree.Program.encodeDictionary key RingProgram.flat seed)
      (key k) (RingProgram.flat value) (Dictionary.codeBranchBudget (baseWidth p t) d)

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width count tail : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ stepBudget p t M cache key seed k x, ∃ rr,
      Eval step n
        (state regs M.bits width count
          (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat seed))
          (Encoding.frame (key k) ++ Encoding.frame (RingProgram.flat x) ++ tail))
        (state rr M.bits width count
          (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
            (Dictionary.insertCode p t M cache k x seed))) tail) := by
  have hr := read_eval regs M.bits width count
    (Squarefree.Program.encodeDictionary key RingProgram.flat seed) (key k) (RingProgram.flat x) tail
  obtain ⟨n,hn,r1,hi⟩ := Dictionary.insert_code_eval p t M cache key hk seed k x
    (readRegs regs 0 1 none) width count hc hw
  have hp := insert_eval hi tail
  have hc := clearCoefficient_eval r1 M.bits width count
    (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
      (Dictionary.insertCode p t M cache k x seed))) (RingProgram.flat x) tail
  have hrun := hr.seq (hp.seq hc)
  refine ⟨_,?_,readRegs r1 0 1 none,hrun⟩
  change _ ≤ 6*(key k).length+11*(RingProgram.flat x).length+15+_
  calc
    _ = (6*(key k).length+11*(RingProgram.flat x).length+15)+n := by omega
    _ ≤ _ := Nat.add_le_add_left hn _

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

abbrev loop : Cmd 8 28 := .while 7 (.seq step peek)
abbrev scan : Cmd 8 28 := .seq peek loop
def program := compiled scan 27 15

def bytes {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) : List Bool :=
  Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat entries)

def ready {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d)) : Data :=
  state (readRegs regs 0 7 (bytes key source).head?) modulus width count (bytes key seed) (bytes key source)

def work (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) :
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d) → ℕ
  | [], _ => 1
  | a::source, seed => stepBudget p t M cache key seed a.1 a.2 + 2 +
      work p t M cache key source (Dictionary.insertCode p t M cache a.1 a.2 seed)

omit [DecidableEq K] in
theorem peek_ready {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d)) :
    Eval peek 1 (state regs modulus width count (bytes key seed) (bytes key source))
      (ready regs modulus width count key seed source) := by
  exact peek_eval _

omit [DecidableEq K] in
theorem ready_nil {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed : List (K × RingProgram.Code (Word B) d)) :
    (ready regs modulus width count key seed []).regs 7 = false := by
  simp [ready,state,extend,Dictionary.machine,readRegs,bytes,
    Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary]

omit [DecidableEq K] in
theorem ready_cons {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d))
    (a : K × RingProgram.Code (Word B) d) :
    (ready regs modulus width count key seed (a::source)).regs 7 = true := by
  cases he : key a.1 <;>
    simp [ready,state,extend,Dictionary.machine,readRegs,bytes,
      Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary,Encoding.frame,he]

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ work p t M cache key source seed, ∃ rr,
      Eval loop n (ready regs M.bits width count key seed source)
        (state rr M.bits width count (bytes key (run p t M cache source seed)) []) := by
  induction source generalizing seed regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 7 none,?_⟩
    exact Eval.while_false (ready_nil regs M.bits width count key seed)
  | cons a source ih =>
    let initial := readRegs regs 0 7 (bytes key (a::source)).head?
    let next := Dictionary.insertCode p t M cache a.1 a.2 seed
    obtain ⟨n,hn,r1,hs⟩ := step_eval p t M cache key hk seed a.1 a.2 initial width count (bytes key source) hc hw
    have hp := peek_ready r1 M.bits width count key next source
    obtain ⟨m,hm,rr,ht⟩ := ih next r1
    have hrun := Eval.while_true (ready_cons regs M.bits width count key seed source a) (hs.seq hp) ht
    refine ⟨_,?_,rr,hrun⟩
    dsimp only [next] at hm
    dsimp [work]
    omega

theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ rr, RunsIn program (work p t M cache key source seed + 2)
      ((state regs M.bits width count (bytes key seed) (bytes key source)).withPC (some program.entry))
      ((state rr M.bits width count (bytes key (run p t M cache source seed)) []).withPC none) := by
  obtain ⟨n,hn,rr,hl⟩ := loop_eval p t M cache key hk source seed regs width count hc hw
  have hr := (peek_ready regs M.bits width count key seed source).seq hl
  exact ⟨rr,1+n+1,by omega,compiled_halt_trace hr 27 15⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

theorem insertCode_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (Dictionary.insertCode p t M cache k x seed)).Nodup := by
  unfold Dictionary.insertCode
  have heq : Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) =
      (Squarefree.Sparse.keys seed).filter (fun j => decide (j ≠ k)) := by
    clear hn
    induction seed with
    | nil => rfl
    | cons a seed ih =>
      by_cases h : a.1=k <;> simpa [Squarefree.Sparse.erase,Squarefree.Sparse.keys,h] using ih
  have he : (Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed)).Nodup := by
    rw [heq]
    exact hn.filter _
  have hnot : k ∉ Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) := by
    rw [heq]
    simp
  simp only [Squarefree.Sparse.keys,List.map_cons,List.map_reverse]
  exact List.nodup_cons.mpr ⟨by simpa [Squarefree.Sparse.keys] using hnot,
    by simpa [Squarefree.Sparse.keys] using he⟩

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache source seed)).Nodup := by
  induction source generalizing seed with
  | nil => exact hn
  | cons a source ih => exact ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn)

theorem insertCode_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :
    (Dictionary.insertCode p t M cache k x seed).length ≤ seed.length+1 := by
  unfold Dictionary.insertCode
  have h := List.length_filter_le (fun a : K × RingProgram.Code (Word (baseWidth p t)) d => decide (a.1 ≠ k)) seed
  simpa [Squarefree.Sparse.erase] using Nat.add_le_add_right h 1

theorem run_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :
    (run p t M cache source seed).length ≤ source.length+seed.length := by
  induction source generalizing seed with
  | nil => simp [run]
  | cons a source ih =>
    have h := ih (Dictionary.insertCode p t M cache a.1 a.2 seed)
    have hl := insertCode_length p t M cache a.1 a.2 seed
    change (run p t M cache source (Dictionary.insertCode p t M cache a.1 a.2 seed)).length ≤ _
    simp only [List.length_cons]
    omega

/-- The streaming machine's output is exactly the sum of source and seed
polynomials, despite the implementation's reversal of stored table order. -/
theorem run_decode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R) (atom : K → R → A)
    (hz : ∀ k, atom k 0 = 0) (ha : ∀ k x y, atom k (x+y) = atom k x + atom k y)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.decode atom (Dictionary.denoteTable f (run p t M cache source seed)) =
      Squarefree.Sparse.decode atom (Dictionary.denoteTable f source) +
      Squarefree.Sparse.decode atom (Dictionary.denoteTable f seed) := by
  dsimp only
  induction source generalizing seed with
  | nil => simp [run,Dictionary.denoteTable,Squarefree.Sparse.decode]
  | cons a source ih =>
    rw [run,ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn),
      Dictionary.insertCode_decode p t M cache scalar basis atom hz ha seed a.1 a.2 hn]
    simp only [Dictionary.denoteTable,List.map_cons,Squarefree.Sparse.decode]
    simp only [add_assoc,add_left_comm]

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def KeyBound {C : Type*} (key : K → List Bool) (W : ℕ) (l : List (K × C)) : Prop :=
  ∀ a ∈ l, (key a.1).length ≤ W

theorem insertCode_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    KeyBound key W (Dictionary.insertCode p t M cache k x seed) := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem stepBudget_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    stepBudget p t M cache key seed k x ≤
      220*(seed.length+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d := by
  let value := match seed.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  have hv : (RingProgram.flat value).length ≤ d*baseWidth p t := by rw [RingProgram.flat_length]
  have h := Dictionary.insertBudget_le (Squarefree.Program.encodeDictionary key RingProgram.flat seed)
    (key k) (RingProgram.flat value) (Dictionary.codeBranchBudget (baseWidth p t) d) W (d*baseWidth p t)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact hs b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2)) hk hv
  simp only [Squarefree.Program.encodeDictionary,List.length_map] at h
  change 6*(key k).length+11*(RingProgram.flat x).length+15+ _ ≤ _
  rw [RingProgram.flat_length]
  change Dictionary.insertBudget _ _ (RingProgram.flat value) _ ≤ _ at h
  dsimp only [value,Squarefree.Program.encodeDictionary] at h ⊢
  nlinarith

/-- A uniform polynomial bound for the complete runtime normalization loop. -/
theorem work_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W N : ℕ)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : KeyBound key W source) (hi : KeyBound key W seed)
    (hn : source.length+seed.length ≤ N) :
    work p t M cache key source seed ≤ source.length *
      (220*(N+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d + 2) + 1 := by
  induction source generalizing seed with
  | nil => simp [work]
  | cons a source ih =>
    have ha := hs a (by simp)
    have htail : KeyBound key W source := fun b hb => hs b (by simp [hb])
    have hnext := insertCode_keyBound p t M cache key W seed a.1 a.2 ha hi
    have hlen := insertCode_length p t M cache a.1 a.2 seed
    have hcap : source.length + (Dictionary.insertCode p t M cache a.1 a.2 seed).length ≤ N := by
      simp only [List.length_cons] at hn; omega
    have hrec := ih _ htail hnext hcap
    have hstep := stepBudget_le p t M cache key W seed a.1 a.2 ha hi
    have hsize : seed.length+1 ≤ N+1 := by simp only [List.length_cons] at hn; omega
    have hmul := Nat.mul_le_mul_right (W+d*baseWidth p t+1) (Nat.mul_le_mul_left 220 hsize)
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

end OAI.Algorithms
