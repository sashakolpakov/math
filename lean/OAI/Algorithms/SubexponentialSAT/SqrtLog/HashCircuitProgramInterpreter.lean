import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLiteralMemory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramRowMemory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMeaning

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one payload left : List (Product.Entry n (baseWidth p t) d))

def negateBudget (degree : List Bool) : ℕ :=
  36*(Product.bytes payload).length + 18*(RingProgram.flat minusOne).length +
  7*(Product.bytes one).length + 9*(Product.bytes (negative p t M cache table minusOne one payload)).length +
  9*degree.length + Squarefree.ScaleProgram.budget Squarefree.encodeIndex payload +
  Normalize.work p t M cache Squarefree.encodeIndex
    (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) one + 73

def budget (degree : List Bool) (u J v : ℕ) (positive : Bool)
    (entries : List (List Bool × List Bool)) : ℕ :=
  8*v+16+literalFetchBudget (Encoding.encodeNat v) entries+9*(Product.bytes payload).length+10 +
  (if positive then negateBudget p t M cache table minusOne one payload degree else 0) + 1 +
  9*(Product.bytes left).length+
  11*(Product.bytes (value p t M cache table minusOne one payload positive)).length+
  9*(Product.bytes (result p t M cache table minusOne one payload left u J positive)).length+
  Product.work p t M cache table u J left (value p t M cache table minusOne one payload positive) []+29+3

def outputHigh (high : Fin 40 → List Bool) (table result : List Bool) : Fin 40 → List Bool :=
  Function.update (literalHigh high [] table) 11 result

theorem eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J v : ℕ) (positive : Bool) (entries : List (List Bool × List Bool))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (hlookup : entries.lookup (Encoding.encodeNat v) = some (Product.bytes payload))
    (h0 : high 0 = []) (h1 : high 1 = []) (h3 : high 3 = []) (h4 : high 4 = []) (h5 : high 5 = [])
    (h2 : high 2 = (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse)
    (h6 : high 6 = Squarefree.Program.lookupRecords entries)
    (hleft : high 11 = Product.bytes left) (hone : high 13 = Product.bytes one)
    (hminus : high 20 = RingProgram.flat minusOne) (htmp : high 14 = []) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ cost ≤ budget p t M cache table minusOne one payload left degree u J v positive entries,
      ∃ rr, Eval (literalStep arithmetic) cost (Memory.state regs (Product.tapes e) high)
        (Memory.state (returned (Memory.state rr (Product.tapes e) high)).regs (Product.tapes e)
          (outputHigh high (Squarefree.Program.lookupRecords entries)
            (Product.bytes (result p t M cache table minusOne one payload left u J positive)))) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let start := Memory.state regs (Product.tapes e) high
  let lookupTable := Squarefree.Program.lookupRecords entries
  have hready : LookupReady start lookupTable := by
    constructor
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h0
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h1
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h3
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h4
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h5
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h6
  have hquery : start.stacks 58 = (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse := by
    simpa [start,Memory.state,Memory.tapes] using h2
  have hproject := project_lookup start
    (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse lookupTable hready hquery
  obtain ⟨nf,hnf,rf,hf,hflag⟩ := fetchLiteral_from_state start (callerRegs start) (start.regs 5)
    positive v (Product.bytes payload) entries hlookup hproject
  let fetched := literalFrame start rf positive [] [] (Product.bytes payload) lookupTable
  let hfHigh := literalHigh high (Product.bytes payload) lookupTable
  have hmem : fetched = Memory.state fetched.regs (Product.tapes e) hfHigh :=
    literalFrame_memory regs (Product.tapes e) high rf positive (Product.bytes payload) lookupTable
  have hsign : fetched.regs 5 = positive :=
    literalFrame_sign start rf positive [] [] (Product.bytes payload) lookupTable
  change Eval fetchLiteral nf start fetched at hf
  rw [hmem] at hf
  let chosen := value p t M cache table minusOne one payload positive
  let hcHigh := Function.update hfHigh (5 : Fin 40) (Product.bytes chosen)
  have hchoose : ∃ nc ≤ (if positive then negateBudget p t M cache table minusOne one payload degree else 0)+1,
      ∃ rc, Eval (.ite 5 complement (.base .skip)) nc
        (Memory.state fetched.regs (Product.tapes e) hfHigh)
        (Memory.state rc (Product.tapes e) hcHigh) := by
    cases hp : positive with
    | false =>
      have hsame : hcHigh = hfHigh := by
        funext i
        by_cases hi : i = 5
        · subst i; simp [hcHigh,hfHigh,chosen,value,hp,literalHigh]
        · simp [hcHigh,hi]
      refine ⟨1,by simp [],fetched.regs,?_⟩
      rw [hsame]
      apply Eval.ite_false (by simpa [Memory.state,hp] using hsign)
      exact Eval.base (StructuredProgram.Eval.skip _)
    | true =>
      obtain ⟨nc,hnc,rc,hcomp⟩ := WeightedCallbacks.complement_eval p t M cache hz table minusOne
        degree width (List.replicate u true) (List.replicate J true) hd hw
        Squarefree.encodeIndex Squarefree.encodeIndex_injective payload one fetched.regs hfHigh
        (by rfl) (by simpa [hfHigh,literalHigh] using hminus)
        (by simpa [hfHigh,literalHigh] using hone) (by simpa [hfHigh,literalHigh] using htmp)
      have hout : WeightedCallbacks.complementedHigh hfHigh
          (Normalize.bytes Squarefree.encodeIndex (negative p t M cache table minusOne one payload)) = hcHigh := by
        funext i; fin_cases i <;> simp [WeightedCallbacks.complementedHigh,hcHigh,chosen,value,hp,negative]
      change Eval complement nc (Memory.state fetched.regs (Product.tapes e) hfHigh)
        (Memory.state rc (Product.tapes e) (WeightedCallbacks.complementedHigh hfHigh
          (Normalize.bytes Squarefree.encodeIndex (negative p t M cache table minusOne one payload)))) at hcomp
      rw [hout] at hcomp
      refine ⟨nc+1,?_,rc,Eval.ite_true (by simpa [Memory.state,hp] using hsign) hcomp⟩
      simpa [hp,negateBudget,hfHigh,literalHigh,hone,hminus,negative,Product.bytes] using Nat.add_le_add_right hnc 1
  obtain ⟨nc,hnc,rc,hchoose⟩ := hchoose
  obtain ⟨np,hnp,rp,hprod⟩ := ProductCallback.eval p t M cache hz table degree width hd hw
    u J left chosen rc hcHigh
    (by simpa [hcHigh,hfHigh,literalHigh] using hleft)
    (by simp [hcHigh]) (by simpa [hcHigh,hfHigh,literalHigh] using htmp)
  let out := outputHigh high lookupTable (Product.bytes (result p t M cache table minusOne one payload left u J positive))
  have hout : ProductCallback.resultHigh hcHigh
      (Product.bytes (Product.run p t M cache table u J left chosen [])) = out := by
    funext i; fin_cases i <;> simp [ProductCallback.resultHigh,hcHigh,hfHigh,literalHigh,outputHigh,out,result,chosen]
  rw [hout] at hprod
  have hreturn := recordReturn_eval (Memory.state rp (Product.tapes e) out)
  refine ⟨nf+nc+np+3,?_,rp,?_⟩
  · dsimp only [budget,result]
    dsimp only [chosen] at hnp
    simp only [Product.bytes] at hnf hnc hnp ⊢
    omega
  · convert hf.seq (hchoose.seq (hprod.seq hreturn)) using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def baseHigh (high : Fin 40 → List Bool) (acc : List Bool) : Fin 40 → List Bool :=
  Function.update (literalHigh high [] (high 6)) 11 acc

def base (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool) (acc : List Bool) : Machine :=
  Memory.state regs (Product.tapes e) (baseHigh high acc)

def recordHigh (high : Fin 40 → List Bool) (acc src payload : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (baseHigh high acc) 7 src) 2 payload

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state literalPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 7) src) (Memory.highPort 2) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

def cost (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  LiteralCallback.budget p t M cache table minusOne one (incidence l.variable) acc degree
    u J l.variable.val l.positive entries

theorem callback_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries l acc,
      ∃ rr, Eval (literalStep arithmetic) k
        (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc))
          false true false tail (literalBits l).reverse)
        (RecordPrograms.state literalPorts
          (base rr e high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))
          false true false tail []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let h0 := recordHigh high (Product.bytes acc) tail (literalBits l).reverse
  obtain ⟨k,hk,rr,he⟩ := LiteralCallback.eval p t M cache table minusOne one (incidence l.variable) acc hz
    degree width hd hw u J l.variable.val l.positive entries r0 h0 (hl l.variable)
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,literalBits,Encoding.literalCode])
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using ht)
    (by simp [h0,recordHigh,baseHigh])
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using ho)
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using hm)
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using htmp)
  have hh : LiteralCallback.outputHigh h0 (Squarefree.Program.lookupRecords entries)
      (Product.bytes (step p t M cache table minusOne one incidence u J l acc)) =
      recordHigh high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)) tail [] := by
    funext i; fin_cases i <;> simp [LiteralCallback.outputHigh,h0,recordHigh,baseHigh,literalHigh,ht]
  change Eval (literalStep arithmetic) k (Memory.state r0 (Product.tapes e) h0)
    (Memory.state (returned (Memory.state rr (Product.tapes e) h0)).regs (Product.tapes e)
      (LiteralCallback.outputHigh h0 (Squarefree.Program.lookupRecords entries)
        (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))) at he
  rw [hh] at he
  refine ⟨k,hk,rr,?_⟩
  rw [record_state,record_state]
  exact he

/-- The fixed clause loop visits every original literal. Its cost recurrence
includes every physical frame read, arithmetic callback and loop branch. -/
theorem command_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ls : List (SAT.Literal (Fin n))) (acc : List (Product.Entry n (baseWidth p t) d))
    (suffix : List Bool) (v pr f : Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := step p t M cache table minusOne one incidence u J
    ∃ k ≤ 3+DynamicFold.work literalBits update (cost p t M cache table minusOne one incidence degree u J entries) ls acc,
      ∃ rr, Eval (clauseLoop arithmetic) k
        (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc)) v pr f
          (Encoding.encodeList id (ls.map literalBits) ++ suffix) [])
        (RecordPrograms.state literalPorts
          (base rr e high (Product.bytes (DynamicFold.value update ls acc))) false true false suffix []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let update := step p t M cache table minusOne one incidence u J
  let charge := cost p t M cache table minusOne one incidence degree u J entries
  let Rep : List (Product.Entry n (baseWidth p t) d) → Machine → Prop :=
    fun a b => ∃ rr, b = base rr e high (Product.bytes a)
  have hc : DynamicFold.Contract literalPorts (literalStep arithmetic) literalBits update charge Rep := by
    intro l a b hb tail
    obtain ⟨rflRegs,rfl⟩ := hb
    obtain ⟨k,hk,rr,he⟩ := callback_eval p t M cache table minusOne one incidence degree u J entries
      hz width hd hw hl rflRegs high ht ho hm htmp l a tail
    exact ⟨k,base rr e high (Product.bytes (update l a)),hk,⟨rr,rfl⟩,he⟩
  obtain ⟨k,next,hk,hn,he⟩ := DynamicFold.command_eval literalPorts (literalStep arithmetic) literalBits
    update charge Rep hc ls acc (base regs e high (Product.bytes acc)) ⟨regs,rfl⟩ suffix v pr f
  obtain ⟨rr,rfl⟩ := hn
  exact ⟨k,hk,rr,he⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def baseHigh (high : Fin 40 → List Bool) (acc : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Clause.baseHigh high []) 7 []) 9 []) 10 []) 12 acc

def base (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool) (acc : List Bool) : Machine :=
  Memory.state regs (Product.tapes e) (baseHigh high acc)

def recordHigh (high : Fin 40 → List Bool) (acc src payload : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (baseHigh high acc) 8 src) 10 payload

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state rowPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 8) src) (Memory.highPort 10) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

private theorem accumulated_recordHigh
    (high : Fin 40 → List Bool) (acc tail payload literals scalar one clause result : List Bool) :
    WeightedCallbacks.accumulatedHigh
        (Clause.recordHigh
          (Function.update (openedHigh (recordHigh high acc tail payload) literals scalar) 11 one)
          clause [] []) result =
      recordHigh high result tail [] := by
  funext i
  fin_cases i <;>
    simp [WeightedCallbacks.accumulatedHigh, Clause.recordHigh, Clause.baseHigh,
      literalHigh, openedHigh, recordHigh, baseHigh]

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

def cost (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) : ℕ :=
  let clause := clauseValue p t M cache table minusOne one incidence u J w
  3*(payload w).length+6*(RingProgram.flat w.scalar).length+8 +
  (7*(Product.bytes one).length+5) +
  (3+DynamicFold.work Clause.literalBits (Clause.step p t M cache table minusOne one incidence u J)
    (Clause.cost p t M cache table minusOne one incidence degree u J entries) w.literals one) +
  (36*(Product.bytes clause).length+14*(RingProgram.flat w.scalar).length+9*(Product.bytes acc).length+
    9*(Product.bytes (value p t M cache table minusOne one incidence u J w acc)).length+9*degree.length+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex clause+
    Normalize.work p t M cache Squarefree.encodeIndex (Squarefree.ScaleProgram.scaled p t M cache table w.scalar clause) acc+74)+3

theorem callback_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries w acc,
      ∃ rr, Eval (weightedClauseStep arithmetic) k
        (RecordPrograms.state rowPorts (base regs e high (Product.bytes acc))
          false true false tail (payload w).reverse)
        (RecordPrograms.state rowPorts
          (base rr e high (Product.bytes (value p t M cache table minusOne one incidence u J w acc)))
          false true false tail []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let h0 := recordHigh high (Product.bytes acc) tail (payload w).reverse
  let start := Memory.state r0 (Product.tapes e) h0
  have hready : WeightedReady start := by
    constructor <;> simp [start,Memory.state,Memory.tapes,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh]
  have hp : start.stacks 66 = (Encoding.frame (RingProgram.flat w.scalar) ++ literalList w).reverse := by
    simp [start,Memory.state,Memory.tapes,h0,recordHigh,payload]
  have hopen := openWeighted_from_state start (RingProgram.flat w.scalar) (literalList w) hready hp
  let openRegs := readRegs (readRegs (rowCallerRegs start) 0 1 none) 0 1 (some false)
  let opened := rowFrame start openRegs [] (literalList w) (RingProgram.flat w.scalar).reverse
  let h1 := openedHigh h0 (literalList w) (RingProgram.flat w.scalar).reverse
  have hopenMemory : opened = Memory.state opened.regs (Product.tapes e) h1 :=
    rowFrame_memory r0 (Product.tapes e) h0 openRegs (literalList w) (RingProgram.flat w.scalar).reverse
  change Eval openWeighted (3*(payload w).length+6*(RingProgram.flat w.scalar).length+8) start opened at hopen
  rw [hopenMemory] at hopen
  have htmp1 : h1 14 = [] := by simpa [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using htmp
  have hcopy := Memory.copy_high_high opened.regs (Product.tapes e) h1 13 11 14
    (by decide) (by decide) (by decide) htmp1
  have hone1 : h1 13 = Product.bytes one := by simpa [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using ho
  have hacc1 : h1 11 = [] := by simp [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh]
  simp only [hone1,hacc1,List.append_nil] at hcopy
  let r1 := readRegs opened.regs 0 1 none
  let h2 := Function.update h1 (11 : Fin 40) (Product.bytes one)
  obtain ⟨kc,hkc,rc,hclause⟩ := Clause.command_eval p t M cache table minusOne one incidence degree u J entries hz
    width hd hw hl r1 h2
    (by simpa [h2,h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using ht)
    (by simpa [h2] using hone1)
    (by simpa [h2,h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using hm)
    (by simpa [h2] using htmp1)
    w.literals one [] (r1 0) (r1 1) (r1 2)
  let clause := clauseValue p t M cache table minusOne one incidence u J w
  let h3 := Clause.recordHigh h2 (Product.bytes clause) [] []
  let r2 := Function.update (Function.update (Function.update rc 0 false) 1 true) 2 false
  have hclauseStart : RecordPrograms.state literalPorts (Clause.base r1 e h2 (Product.bytes one))
      (r1 0) (r1 1) (r1 2) (Encoding.encodeList id (w.literals.map Clause.literalBits) ++ []) [] =
      Memory.state r1 (Product.tapes e) h2 := by
    rw [Clause.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · simp
    · apply congrArg (Memory.tapes (Product.tapes e))
      funext i; fin_cases i <;> simp [Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh,literalList]
  rw [hclauseStart,Clause.record_state] at hclause
  change Eval (clauseLoop arithmetic) kc (Memory.state r1 (Product.tapes e) h2)
    (Memory.state r2 (Product.tapes e) h3) at hclause
  obtain ⟨ka,hka,ra,hacc⟩ := WeightedCallbacks.accumulate_eval p t M cache hz table w.scalar degree width
    (List.replicate u true) (List.replicate J true) hd hw Squarefree.encodeIndex Squarefree.encodeIndex_injective
    clause acc r2 h3
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,Product.bytes,Normalize.bytes,Squarefree.ScaleProgram.encode])
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh])
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh])
    (by simpa [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2] using htmp1)
  let result := value p t M cache table minusOne one incidence u J w acc
  let h4 := recordHigh high (Product.bytes result) tail []
  have hfinish : WeightedCallbacks.accumulatedHigh h3 (Product.bytes result) = h4 := by
    simpa [h3,h4,h2,h1,h0] using accumulated_recordHigh high (Product.bytes acc)
      tail (payload w).reverse (literalList w) (RingProgram.flat w.scalar).reverse
      (Product.bytes one) (Product.bytes clause) (Product.bytes result)
  change Eval accumulate ka (Memory.state r2 (Product.tapes e) h3)
    (Memory.state ra (Product.tapes e) (WeightedCallbacks.accumulatedHigh h3 (Product.bytes result))) at hacc
  rw [hfinish] at hacc
  have hreturn := recordReturn_eval (Memory.state ra (Product.tapes e) h4)
  refine ⟨(3*(payload w).length+6*(RingProgram.flat w.scalar).length+8)+(7*(Product.bytes one).length+5)+kc+ka+3,?_,ra,?_⟩
  · dsimp only [cost]
    have h11 : h3 11 = Product.bytes clause := by simp [h3,Clause.recordHigh,Clause.baseHigh]
    have h9 : h3 9 = (RingProgram.flat w.scalar).reverse := by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh]
    have h12 : h3 12 = Product.bytes acc := by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh]
    rw [h11,h9,h12,List.length_reverse] at hka
    dsimp only [clause,result,clauseValue,value,Product.bytes] at hka hkc ⊢
    omega
  · rw [record_state,record_state]
    convert hopen.seq (hcopy.seq (hclause.seq (hacc.seq hreturn))) using 1 <;> first | rfl | omega

/-- Every weighted clause is read from the supplied row and executed once. -/
theorem loop_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ws : List (WeightedClause n (baseWidth p t) d)) (acc : List (Product.Entry n (baseWidth p t) d))
    (suffix : List Bool) (v pr f : Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := value p t M cache table minusOne one incidence u J
    ∃ k ≤ 3+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws acc,
      ∃ rr, Eval (rowLoop arithmetic) k
        (RecordPrograms.state rowPorts (base regs e high (Product.bytes acc)) v pr f
          (Encoding.encodeList id (ws.map payload) ++ suffix) [])
        (RecordPrograms.state rowPorts
          (base rr e high (Product.bytes (DynamicFold.value update ws acc))) false true false suffix []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let update := value p t M cache table minusOne one incidence u J
  let charge := cost p t M cache table minusOne one incidence degree u J entries
  let Rep : List (Product.Entry n (baseWidth p t) d) → Machine → Prop :=
    fun a b => ∃ rr, b = base rr e high (Product.bytes a)
  have hc : DynamicFold.Contract rowPorts (weightedClauseStep arithmetic) payload update charge Rep := by
    intro w a b hb tail
    obtain ⟨rflRegs,rfl⟩ := hb
    obtain ⟨k,hk,rr,he⟩ := callback_eval p t M cache table minusOne one incidence degree u J entries
      hz width hd hw hl rflRegs high ht ho hm htmp w a tail
    exact ⟨k,base rr e high (Product.bytes (update w a)),hk,⟨rr,rfl⟩,he⟩
  obtain ⟨k,next,hk,hn,he⟩ := DynamicFold.command_eval rowPorts (weightedClauseStep arithmetic) payload
    update charge Rep hc ws acc (base regs e high (Product.bytes acc)) ⟨regs,rfl⟩ suffix v pr f
  obtain ⟨rr,rfl⟩ := hn
  exact ⟨k,hk,rr,he⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

theorem program_runs (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ws : List (WeightedClause n (baseWidth p t) d)) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := value p t M cache table minusOne one incidence u J
    let input := Encoding.encodeList id (ws.map payload)
    ∃ rr, RunsIn Native.program
      (7+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws [])
      ((RecordPrograms.state rowPorts (base regs e high []) false true false input []).withPC
        (some Native.program.entry))
      ((RecordPrograms.state rowPorts
        (base rr e high (Product.bytes (DynamicFold.value update ws []))) false true false [] []).withPC none) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let input := Encoding.encodeList id (ws.map payload)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let r1 := readRegs r0 0 1 none
  let h0 := recordHigh high [] input []
  have hzero : h0 12 = [] := by simp [h0,recordHigh,baseHigh]
  have hsame : Function.update h0 (12 : Fin 40) [] = h0 := by
    rw [← hzero]
    exact Function.update_eq_self 12 h0
  have clearRun := Memory.clear_high r0 (Product.tapes e) h0 12
  simp only [hzero,hsame] at clearRun
  have hclear : Eval (clear 68) 3
      (RecordPrograms.state rowPorts (base regs e high []) false true false input [])
      (RecordPrograms.state rowPorts (base r1 e high []) (r1 0) (r1 1) (r1 2) input []) := by
    rw [record_state,record_state]
    rw [show Memory.highPort 12 = (68 : Fin 96) by decide] at clearRun
    simpa only [r0,r1,h0,List.length_nil,Nat.mul_zero,zero_add,
      Function.update_eq_self] using clearRun
  obtain ⟨k,hk,rr,he⟩ := loop_eval p t M cache table minusOne one incidence degree u J entries hz
    width hd hw hl r1 high ht ho hm htmp ws [] [] (r1 0) (r1 1) (r1 2)
  simp only [List.append_nil] at he
  have hrun : Eval Native.command (3+k)
      (RecordPrograms.state rowPorts (base regs e high []) false true false input [])
      (RecordPrograms.state rowPorts
        (base rr e high (Product.bytes (DynamicFold.value
          (value p t M cache table minusOne one incidence u J) ws []))) false true false [] []) :=
    hclear.seq he
  exact ⟨rr,3+k+1,by omega,compiled_halt_trace hrun 64 68⟩

/-- The final physical output port is exactly the computed sparse dictionary. -/
theorem result_stack (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (result : List Bool) :
    (RecordPrograms.state rowPorts (base regs e high result) false true false [] []).stacks 68 = result := by
  simp [RecordPrograms.state,rowPorts,base,Memory.state,Memory.tapes,baseHigh]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
