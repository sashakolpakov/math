import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramFetch

namespace OAI.Algorithms

/-! Commit the native sum as the next accumulator, reclaiming all temporary
strings. The dictionary and query are preserved for the runtime loop. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

abbrev commit : Cmd 8 27 := .seq (clear 17) (.seq (transfer 0 26) (transfer 26 17))

theorem commit_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc out : List Bool) :
    ∃ rr, Eval commit (2*acc.length+6*out.length+9)
      (machine regs (fetchedTape modulus width count entries query acc out))
      (machine rr (inputTape modulus width count entries query out)) := by
  let a := fetchedTape modulus width count entries query acc out
  let a1 : Tape := { a with coeff := [] }
  let a2 : Tape := { a1 with out := [], combined := out.reverse }
  let a3 := inputTape modulus width count entries query out
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 : Eval (clear 17) (2*acc.length+3) (machine regs a) (machine r1 a1) := by
    apply clear_machine regs a a1 17
    funext i; fin_cases i <;> simp [clearStacks,tapes,a,a1,fetchedTape,inputTape]
  have h2 : Eval (transfer 0 26) (3*out.length+3) (machine r1 a1) (machine r2 a2) := by
    apply transfer_machine r1 a1 a2 0 26 (by decide)
    funext i; fin_cases i <;> simp [transferStacks,tapes,a,a1,a2,fetchedTape,inputTape]
  have h3 : Eval (transfer 26 17) (3*out.reverse.length+3) (machine r2 a2)
      (machine (readRegs r2 0 1 none) a3) := by
    apply transfer_machine r2 a2 a3 26 17 (by decide)
    funext i; fin_cases i <;> simp [transferStacks,tapes,a,a1,a2,a3,fetchedTape,inputTape]
  refine ⟨readRegs r2 0 1 none, ?_⟩
  convert h1.seq (h2.seq h3) using 1 ; simp ; omega

abbrev accumulate : Cmd 8 27 := .seq fetchAdd commit

def accumulateBudget (B d : ℕ) (entries : List (List Bool × List Bool))
    (query : List Bool) : ℕ :=
  fetchBudget entries query (codeBranchBudget B d) + 8*(d*B)+9

theorem accumulate_eval {K : Type*} [DecidableEq K]
    (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p e) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    ∃ n ≤ accumulateBudget (baseWidth p e) d encoded (key k), ∃ rr,
      Eval accumulate n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat acc)))
        (machine rr (inputTape M.bits width count encoded (key k)
          (RingProgram.flat (addFetched p e M cache entries k acc)))) := by
  dsimp only
  obtain ⟨n,hn,r1,h1⟩ := fetchAdd_code p e M cache key hk entries k acc regs width count hc hw
  obtain ⟨r2,h2⟩ := commit_eval r1 M.bits width count
    (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) (RingProgram.flat acc)
    (RingProgram.flat (addFetched p e M cache entries k acc))
  refine ⟨_, ?_, r2, h1.seq h2⟩
  simp only [RingProgram.flat_length]
  dsimp [accumulateBudget]
  omega

abbrev accumulateProgram : Program 8 27 (size accumulate+1) := compiled accumulate 15 17

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
