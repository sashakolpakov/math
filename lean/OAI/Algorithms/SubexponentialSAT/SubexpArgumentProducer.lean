import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentSerialization
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentCost

namespace OAI.Algorithms

/-!
# Beta and cached Taylor coefficients to a raw Ce literal

The input negative-beta word is absent. This fixed program first runs actual
quartic negation, then reads the coordinate-major cache and emits the raw
argument. The cache and original beta are preserved.
-/
namespace SubexponentialSAT.SubexpArgumentProducer

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Bits := List Bool

def extras (cache dimension keyWidth output : Bits) : Fin 22 → Bits :=
  fun i => if i=0 then cache else if i=1 then dimension else if i=2 then keyWidth
    else if i=3 then output else []

def state (regs : Fin 8 → Bool) (native : Fin 24 → Bits) (extra : Fin 22 → Bits) : State 8 46 :=
  ⟨regs,Fin.addCases (motive:=fun _ : Fin (24+22) => Bits) native extra⟩

def negPorts : Fin 24 → Fin 46 := Fin.castAdd 22

def cachePorts (i : Fin 24) : Fin 46 :=
  if i=0 then 18 else if i=1 then 19 else ⟨i.val+22,by omega⟩

theorem negPorts_injective : Function.Injective negPorts := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 46 => x.val) h

theorem cachePorts_injective : Function.Injective cachePorts := by decide

def negProgram := ProgramLinking.liftProgram SubexpQuarticFlatNeg.program id negPorts
def cacheProgram := ProgramLinking.liftProgram SubexpCacheArgument.program id cachePorts

abbrev command : Cmd 8 46 := .seq (.call negProgram) (.call cacheProgram)
def program := compiled command 18 27

theorem embed_neg (oldRegs regs : Fin 8 → Bool) (oldNative native : Fin 24 → Bits)
    (extra : Fin 22 → Bits) :
    embedState id negPorts (state oldRegs oldNative extra) ⟨regs,native⟩ = state regs native extra := by
  apply embedState_eq _ _ Function.injective_id negPorts_injective
  · intros; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i hi
    have hn : ¬i.val < 24 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,rfl⟩
    simp [state,Fin.addCases,hn]

@[simp] theorem flags_eta (regs : Fin 8 → Bool) :
    SubexpCacheArgument.flags (regs 0) (regs 1) (regs 2) (regs 3)
      (regs 4) (regs 5) (regs 6) (regs 7) = regs := by
  funext i; fin_cases i <;> rfl

def cacheExtra (columns : List (List Bits)) (B : ℕ) (output : Bits) : Fin 22 → Bits :=
  extras (Encoding.encodeList id (SubexpCacheArgument.columnRecords columns))
    (List.replicate columns.length true) (List.replicate B true) output

theorem embed_cache {W : ℕ} (a negative : Quad (Word W)) (one : Word W)
    (modulus width : Bits) (columns : List (List Bits)) (B : ℕ)
    (oldRegs regs : Fin 8 → Bool) (oldOutput output : Bits) :
    embedState id cachePorts
      (state oldRegs (SubexpQuarticFlatNeg.finalStore a negative one modulus width)
        (cacheExtra columns B oldOutput))
      (SubexpCacheArgument.ready regs
        (SubexpCacheArgument.cacheInputs (SubexpQuarticFlatNeg.flat a) (SubexpQuarticFlatNeg.flat negative) columns B)
        output [] [] [] [] 0 0 0) =
      state regs (SubexpQuarticFlatNeg.finalStore a negative one modulus width)
        (cacheExtra columns B output) := by
  apply embedState_eq _ _ Function.injective_id cachePorts_injective
  · intros; rfl
  · intro i; fin_cases i <;>
      simp [state,cachePorts,cacheExtra,extras,Fin.addCases,
        SubexpCacheArgument.ready,SubexpCacheArgument.cacheInputs,
        SubexpQuarticFlatNeg.finalStore,SubexpQuarticFlatNeg.bankStore,
        SubexpQuarticFlatNeg.emptyBank]
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i hi
    have h27 : i ≠ 27 := fun h => hi ⟨5,h.symm⟩
    fin_cases i <;> first | contradiction | simp [state, cacheExtra, Fin.addCases]

/-- The complete actual program computes negative beta before serialization.
Only beta, the preserved ring constants, and the physical Taylor cache are inputs. -/
theorem program_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : Bits) (hw : width.length=baseWidth p μ) (columns : List (List Bits)) (B : ℕ)
    (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program
      (25000*(baseWidth p μ+1)^2 +
        SubexpCacheArgument.totalCost (SubexpQuarticFlatNeg.flat a)
          (SubexpQuarticFlatNeg.flat (SubexpQuarticNegMachine.negateWords p μ M one a)) columns B + 2)
      ((state regs (SubexpQuarticFlatNeg.initialStore a one M.bits width)
        (cacheExtra columns B [false])).withPC (some program.entry))
      ((state rf (SubexpQuarticFlatNeg.finalStore a (SubexpQuarticNegMachine.negateWords p μ M one a)
        one M.bits width)
        (cacheExtra columns B
          (SubexpCacheArgument.resultBits (SubexpQuarticFlatNeg.flat a)
            (SubexpQuarticFlatNeg.flat (SubexpQuarticNegMachine.negateWords p μ M one a)) columns B [false]))).withPC none) := by
  let negative := SubexpQuarticNegMachine.negateWords p μ M one a
  let extra := cacheExtra columns B [false]
  let before := state regs (SubexpQuarticFlatNeg.initialStore a one M.bits width) extra
  obtain ⟨rn,n,hn,ht⟩ := SubexpQuarticFlatNeg.program_run p μ M a one width hw regs
  have hneg := eval_call_lifted SubexpQuarticFlatNeg.program id negPorts before
    Function.injective_id negPorts_injective
    (a := ⟨regs,SubexpQuarticFlatNeg.initialStore a one M.bits width⟩)
    (b := ⟨rn,SubexpQuarticFlatNeg.finalStore a negative one M.bits width⟩) ht
  simp only [before,embed_neg] at hneg
  obtain ⟨vf,pf,uf,hcache⟩ := SubexpCacheArgument.program_trace
    (SubexpQuarticFlatNeg.flat a) (SubexpQuarticFlatNeg.flat negative) columns B
    (rn 0) (rn 1) (rn 2) (rn 3) (rn 4) (rn 5) (rn 6) (rn 7) [false]
  simp only [flags_eta] at hcache
  let rf := SubexpCacheArgument.flags vf pf true uf (rn 4) false true (rn 7)
  let middle := state rn (SubexpQuarticFlatNeg.finalStore a negative one M.bits width) extra
  have hc := eval_call_lifted SubexpCacheArgument.program id cachePorts middle
    Function.injective_id cachePorts_injective hcache
  simp only [middle,extra,embed_cache] at hc
  have total : Eval command
      (n+(SubexpCacheArgument.totalCost (SubexpQuarticFlatNeg.flat a)
        (SubexpQuarticFlatNeg.flat negative) columns B+1)) before
      (state rf (SubexpQuarticFlatNeg.finalStore a negative one M.bits width)
        (cacheExtra columns B (SubexpCacheArgument.resultBits (SubexpQuarticFlatNeg.flat a)
          (SubexpQuarticFlatNeg.flat negative) columns B [false]))) := hneg.seq hc
  refine ⟨rf,_,?_,compiled_halt_trace total 18 27⟩
  dsimp only [negative]
  omega

/-- Specialization to an actual finite Taylor cache. Negative beta is computed
by the first program call and the output is the serialized raw coefficient list. -/
theorem compileColumns_run {D q : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : Bits) (hw : width.length=baseWidth p μ)
    (taylor : Fin (q+1) → Fin D → Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) :
    let negative := SubexpQuarticNegMachine.negateWords p μ M one a
    let columns := List.ofFn (fun i => List.ofFn (fun j => SubexpQuarticFlatNeg.flat (taylor j i)))
    let B := SubexpSymbolicCost.indexBits D
    ∃ rf, RunsIn program
      (25000*(baseWidth p μ+1)^2 +
        SubexpCacheArgument.totalCost (SubexpQuarticFlatNeg.flat a)
          (SubexpQuarticFlatNeg.flat negative) columns B + 2)
      ((state regs (SubexpQuarticFlatNeg.initialStore a one M.bits width)
        (cacheExtra columns B [false])).withPC (some program.entry))
      ((state rf (SubexpQuarticFlatNeg.finalStore a negative one M.bits width)
        (cacheExtra columns B
          (Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpQuarticFlatNeg.flat)
            (SubexpColumnArgumentCode.compileColumns a negative taylor).reverse))).withPC none) := by
  dsimp only
  obtain ⟨rf,h⟩ := program_run p μ M a one width hw
    (List.ofFn (fun i => List.ofFn (fun j => SubexpQuarticFlatNeg.flat (taylor j i))))
    (SubexpSymbolicCost.indexBits D) regs
  rw [SubexpCacheArgument.resultBits_compileColumns] at h
  exact ⟨rf,h⟩

/-- All growing parameters in the producer's primitive-step bound. `W` is
one base-ring word width, so each quartet occupies `4*W` bits. -/
def finiteCostBound (D q W : ℕ) : ℕ :=
  25000*(W+1)^2 + (88+92*D*(q+1))*(4*W) +
    D*(q+1)*(33*(D+(q+1))+32*SubexpSymbolicCost.indexBits D+275) +
    130*D+64*SubexpSymbolicCost.indexBits D+450

theorem finiteCost_le {D q W : ℕ} (a negative : Quad (Word W))
    (taylor : Fin (q+1) → Fin D → Quad (Word W)) :
    25000*(W+1)^2 +
      SubexpCacheArgument.totalCost (SubexpQuarticFlatNeg.flat a)
        (SubexpQuarticFlatNeg.flat negative)
        (List.ofFn (fun i => List.ofFn (fun j => SubexpQuarticFlatNeg.flat (taylor j i))))
        (SubexpSymbolicCost.indexBits D) + 2 ≤ finiteCostBound D q W := by
  let columns := List.ofFn (fun i => List.ofFn (fun j => SubexpQuarticFlatNeg.flat (taylor j i)))
  have hN : ∀ cs ∈ columns, cs.length ≤ q+1 := by
    intro cs hcs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hcs
    simp
  have hW : ∀ cs ∈ columns, ∀ c ∈ cs, c.length ≤ 4*W := by
    intro cs hcs c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hcs
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    simp
  have h := SubexpCacheArgument.totalCost_uniform
    (SubexpQuarticFlatNeg.flat a) (SubexpQuarticFlatNeg.flat negative)
    columns (SubexpSymbolicCost.indexBits D) (q+1) (4*W) hN hW (by simp) (by simp)
  simp only [columns,List.length_ofFn] at h
  unfold finiteCostBound
  omega

noncomputable section

def decode (p μ : ℕ) (c : Fin 4 → ZMod (p^μ)) (a : Quad (Word (baseWidth p μ))) :=
  quotientDenote c (a.map (wordValue p μ))

/-- The arithmetic premise concerns only the prepared minus-one constant.
The negative-beta equality is derived from the executed quartic negation code. -/
theorem produced_denote {D q : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (one : Word (baseWidth p μ))
    (hone : wordValue p μ one = -1) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ)))
    (taylor : Fin (q+1) → Fin D → Quad (Word (baseWidth p μ))) :
    SymbolicCost.denote
      ((SubexpColumnArgumentCode.compileColumns a (SubexpQuarticNegMachine.negateWords p μ M one a) taylor).map
        (fun term => (term.1,decode p μ c term.2))) =
      SymbolicCost.denote (SubexpArgumentCode.compileArgument (decode p μ c a)
        (fun j i => decode p μ c (taylor j i))) := by
  apply SubexpColumnArgumentCode.decoded_denote_eq
  exact SubexpQuarticNegMachine.negateWords_quotient p μ M one a hone c

/-- The reverse order physically emitted by the stack program has exactly
the same decoded incidence polynomial. -/
theorem produced_reversed_denote {D q : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (one : Word (baseWidth p μ))
    (hone : wordValue p μ one = -1) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ)))
    (taylor : Fin (q+1) → Fin D → Quad (Word (baseWidth p μ))) :
    SymbolicCost.denote
      ((SubexpColumnArgumentCode.compileColumns a (SubexpQuarticNegMachine.negateWords p μ M one a) taylor).reverse.map
        (fun term => (term.1,decode p μ c term.2))) =
      SymbolicCost.denote (SubexpArgumentCode.compileArgument (decode p μ c a)
        (fun j i => decode p μ c (taylor j i))) := by
  rw [List.map_reverse,SubexpArgumentCode.denote_eq_sum,List.map_reverse,List.sum_reverse]
  rw [← SubexpArgumentCode.denote_eq_sum]
  exact produced_denote p μ M one hone c a taylor

/-- Composition point for the physical Taylor-cache generator: its local
coefficient theorem identifies the executed producer with the manuscript's
row argument. No final-polynomial equality is assumed. -/
theorem produced_rowArgument {D q : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (one : Word (baseWidth p μ))
    (hone : wordValue p μ one = -1) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ)))
    (taylor : Fin (q+1) → Fin D → Quad (Word (baseWidth p μ)))
    (θ : LiftRing.Extension (QuarticSearch.poly c))
    (row : Fin D → Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (htaylor : ∀ j i, decode p μ c (taylor j i) =
      ((row i).comp (Polynomial.X + Polynomial.C θ)).coeff j.val) :
    SymbolicCost.denote
      ((SubexpColumnArgumentCode.compileColumns a (SubexpQuarticNegMachine.negateWords p μ M one a) taylor).reverse.map
        (fun term => (term.1,decode p μ c term.2))) =
      Counting.rowArgument row θ (decode p μ c a) q := by
  exact (produced_reversed_denote p μ M one hone c a taylor).trans
    (SubexpArgumentCode.denote_compileArgument_eq_rowArgument (decode p μ c a) θ
      (fun j i => decode p μ c (taylor j i)) row htaylor)

end

end SubexponentialSAT.SubexpArgumentProducer

end OAI.Algorithms
