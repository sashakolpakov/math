import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryHit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryFinish

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def inputTape (modulus width count : List Bool) (entries : List (List Bool × List Bool))
    (query coeff : List Bool) : Tape :=
  { modulus := modulus, width := width, count := count,
    dict := Squarefree.Program.rawEntries entries, query := query.reverse, coeff := coeff }

def outputTape (modulus width count dict coeff : List Bool) : Tape :=
  { modulus := modulus, width := width, count := count, dict := dict, coeff := coeff }

def insertBudget (entries : List (List Bool × List Bool)) (query result : List Bool) (branch : ℕ) : ℕ :=
  7 * (Squarefree.Program.rawEntries entries).length + Squarefree.Program.lookupBudget query entries +
  branch + finishBudget entries query result (Squarefree.Program.rawEntries entries) + 9

theorem insert_miss_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hmiss : entries.lookup query = none) :
    ∃ n ≤ insertBudget entries query coeff (7 * coeff.length + 5), ∃ rr,
      Eval insert n (machine regs (inputTape modulus width count entries query coeff))
        (machine rr (outputTape modulus width count (updatedBytes entries query coeff) coeff)) := by
  let a := inputTape modulus width count entries query coeff
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
  obtain ⟨m,hmBound,rr,hf⟩ := finish_eval (readRegs r3 0 1 none) a3 entries query coeff rfl rfl rfl rfl rfl
  have run := hp.seq (hl.seq (hbranch.seq hf))
  refine ⟨_, ?_, rr, (by simpa [insert,onMiss,finish,a,a1,a2,a3,r1,r3,inputTape,outputTape,hmiss,
    Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult] using run)⟩
  have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
    simpa only [rawEntries_eq_lookupRecords] using htail
  dsimp [a,a1,a2,a3,inputTape,insertBudget,finishBudget] at hn hmBound ⊢
  omega

theorem insert_hit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (entries : List (List Bool × List Bool)) (query : List Bool)
    (hhit : entries.lookup query = some (RingScan.rightBits pairs))
    (hc : count.length = pairs.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ insertBudget entries query (RingScan.sumBits p t M pairs) (hitBudget p t pairs), ∃ rr,
      Eval insert n (machine regs (inputTape M.bits width count entries query (RingScan.leftBits pairs)))
        (machine rr (outputTape M.bits width count
          (updatedBytes entries query (RingScan.sumBits p t M pairs)) (RingScan.leftBits pairs))) := by
  let a := inputTape M.bits width count entries query (RingScan.leftBits pairs)
  let a1 : Tape := { a with remain := a.dict }
  let r1 := readRegs regs 0 1 none
  have hp := copyDict_eval regs a rfl
  obtain ⟨n,hn,r2,tail,hl,hflag,htail⟩ := lookup_eval r1 a1 query entries rfl
    (rawEntries_eq_lookupRecords entries) rfl
  let r3 := overlay r1 r2
  let a2 : Tape := { a1 with remain := tail, found := Squarefree.Program.lookupResult (entries.lookup query) }
  obtain ⟨k,hk,r4,hh⟩ := onHit_eval p t M pairs r3 a2 rfl rfl
    (by simp [a2,hhit,Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult])
    rfl rfl rfl rfl hc hw
  have hb : (machine r3 a2).regs 4 = true := by
    change overlay r1 r2 (smallRegs 4) = true
    rw [show overlay r1 r2 (smallRegs 4) = r2 4 from smallRegs_injective.extend_apply _ _ _]
    simpa only [hhit,Option.isSome_some] using hflag
  have hbranch := Eval.ite_true (no := onMiss) hb hh
  let a3 : Tape := { a2 with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs }
  obtain ⟨m,hmBound,rr,hf⟩ := finish_eval r4 a3 entries query (RingScan.sumBits p t M pairs) rfl rfl rfl rfl rfl
  have run := hp.seq (hl.seq (hbranch.seq hf))
  refine ⟨_, ?_, rr, (by simpa [insert,finish,a,a1,a2,a3,r1,r3,inputTape,outputTape] using run)⟩
  have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
    simpa only [rawEntries_eq_lookupRecords] using htail
  dsimp [a,a1,a2,a3,inputTape,insertBudget,finishBudget] at hn hmBound ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
