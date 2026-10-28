import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryCode

namespace OAI.Algorithms

/-! A paid dictionary scan followed by native vector addition. A missing
coefficient contributes zero and leaves the accumulator unchanged. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

abbrev fetchAdd : Cmd 8 27 :=
  .seq (copy 15 18 23)
    (.seq lookup (.seq (.ite 4 onHit onMiss) (clear 18)))

def fetchBudget (entries : List (List Bool × List Bool)) (query : List Bool)
    (branch : ℕ) : ℕ :=
  9*(Squarefree.Program.rawEntries entries).length +
    Squarefree.Program.lookupBudget query entries + branch + 12

def fetchedTape (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc out : List Bool) : Tape :=
  { inputTape modulus width count entries query acc with out := out }

theorem fetchAdd_miss (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc : List Bool)
    (hmiss : entries.lookup query = none) :
    ∃ n ≤ fetchBudget entries query (7*acc.length+5), ∃ rr,
      Eval fetchAdd n (machine regs (inputTape modulus width count entries query acc))
        (machine rr (fetchedTape modulus width count entries query acc acc)) := by
  let a := inputTape modulus width count entries query acc
  let a1 : Tape := { a with remain := a.dict }
  let r1 := readRegs regs 0 1 none
  have hp := copyDict_eval regs a rfl
  obtain ⟨n,hn,r2,tail,hl,hflag,htail⟩ := lookup_eval r1 a1 query entries rfl
    (rawEntries_eq_lookupRecords entries) rfl
  let r3 := overlay r1 r2
  let a2 : Tape := { a1 with remain := tail, found := Squarefree.Program.lookupResult (entries.lookup query) }
  have hm := copyMiss_eval r3 a2 rfl
  have hb : (machine r3 a2).regs 4 = false := by
    change overlay r1 r2 (smallRegs 4) = false
    rw [show overlay r1 r2 (smallRegs 4) = r2 4 from smallRegs_injective.extend_apply _ _ _]
    simpa only [hmiss,Option.isSome_none] using hflag
  have hbranch := Eval.ite_false (yes := onHit) hb hm
  let a3 : Tape := { a2 with out := a2.coeff }
  have hc := clearRemain_eval (readRegs r3 0 1 none) a3
  have he := hp.seq (hl.seq (hbranch.seq hc))
  refine ⟨7*a.dict.length+5+(n+(7*a2.coeff.length+5+1+(2*a3.remain.length+3))),
    ?_,readRegs (readRegs r3 0 1 none) 0 1 none,?_⟩
  · have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
      simpa only [rawEntries_eq_lookupRecords] using htail
    dsimp [a,a1,a2,a3,inputTape,fetchBudget] at hn ⊢
    omega
  · simpa [fetchAdd,onMiss,a,a1,a2,a3,r1,r3,inputTape,fetchedTape,hmiss,
      Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult] using he

theorem fetchAdd_hit (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (pairs : List (Word (baseWidth p e) × Word (baseWidth p e)))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (entries : List (List Bool × List Bool)) (query : List Bool)
    (hhit : entries.lookup query = some (RingScan.rightBits pairs))
    (hc : count.length = pairs.length) (hw : width.length = baseWidth p e) :
    ∃ n ≤ fetchBudget entries query (hitBudget p e pairs), ∃ rr,
      Eval fetchAdd n (machine regs
        (inputTape M.bits width count entries query (RingScan.leftBits pairs)))
        (machine rr (fetchedTape M.bits width count entries query
          (RingScan.leftBits pairs) (RingScan.sumBits p e M pairs))) := by
  let a := inputTape M.bits width count entries query (RingScan.leftBits pairs)
  let a1 : Tape := { a with remain := a.dict }
  let r1 := readRegs regs 0 1 none
  have hp := copyDict_eval regs a rfl
  obtain ⟨n,hn,r2,tail,hl,hflag,htail⟩ := lookup_eval r1 a1 query entries rfl
    (rawEntries_eq_lookupRecords entries) rfl
  let r3 := overlay r1 r2
  let a2 : Tape := { a1 with remain := tail, found := Squarefree.Program.lookupResult (entries.lookup query) }
  obtain ⟨k,hk,r4,hh⟩ := onHit_eval p e M pairs r3 a2 rfl rfl
    (by simp [a2,hhit,Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult])
    rfl rfl rfl rfl hc hw
  have hb : (machine r3 a2).regs 4 = true := by
    change overlay r1 r2 (smallRegs 4) = true
    rw [show overlay r1 r2 (smallRegs 4) = r2 4 from smallRegs_injective.extend_apply _ _ _]
    simpa only [hhit,Option.isSome_some] using hflag
  have hbranch := Eval.ite_true (no := onMiss) hb hh
  let a3 : Tape := { a2 with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p e M pairs }
  have hf := clearRemain_eval r4 a3
  have he := hp.seq (hl.seq (hbranch.seq hf))
  refine ⟨7*a.dict.length+5+(n+(k+1+(2*a3.remain.length+3))),
    ?_,readRegs r4 0 1 none,?_⟩
  · have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
      simpa only [rawEntries_eq_lookupRecords] using htail
    dsimp [a,a1,a2,a3,inputTape,fetchBudget] at hn ⊢
    omega
  · simpa [fetchAdd,a,a1,a2,a3,r1,r3,inputTape,fetchedTape] using he

variable {K : Type*} [DecidableEq K]

def addFetched (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d) :=
  match entries.lookup k with
  | none => acc
  | some x => (RingProgram.addRun (RingProgram.scalarProgram p e M cache) acc x).1

theorem fetchAdd_code (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p e) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    ∃ n ≤ fetchBudget encoded (key k) (codeBranchBudget (baseWidth p e) d), ∃ rr,
      Eval fetchAdd n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat acc)))
        (machine rr (fetchedTape M.bits width count encoded (key k) (RingProgram.flat acc)
          (RingProgram.flat (addFetched p e M cache entries k acc)))) := by
  dsimp only
  cases he : entries.lookup k with
  | none =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) = none := by
      rw [lookup_encode key RingProgram.flat hk,he]; rfl
    obtain ⟨n,hn,rr,hr⟩ := fetchAdd_miss regs M.bits width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) (RingProgram.flat acc) hl
    refine ⟨n,?_,rr,?_⟩
    · have hb : 7*(RingProgram.flat acc).length+5 ≤ codeBranchBudget (baseWidth p e) d := by
        rw [RingProgram.flat_length]
        dsimp [codeBranchBudget]
        nlinarith [Nat.zero_le (d*(6000*(baseWidth p e+1)^2))]
      dsimp [fetchBudget] at hn ⊢
      omega
    · simpa only [addFetched,he] using hr
  | some x =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) =
        some (RingScan.rightBits (codePairs acc x)) := by
      rw [lookup_encode key RingProgram.flat hk,he,rightBits_codePairs]; rfl
    obtain ⟨n,hn,rr,hr⟩ := fetchAdd_hit p e M (codePairs acc x) regs width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) hl
      (by simpa only [codePairs,List.length_ofFn] using hc) hw
    refine ⟨n,?_,rr,?_⟩
    · simpa only [hitBudget_codePairs] using hn
    · simpa only [addFetched,he,leftBits_codePairs,sumBits_codePairs p e M cache] using hr

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
