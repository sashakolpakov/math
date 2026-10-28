import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramBoot
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramEncoded

namespace OAI.Algorithms

/-! One fixed native preparation command accepts only the runtime binary
precision. It constructs its modulus, scalar cache, table, arrays and counters
with charged bit instructions, ready for the fixed Newton program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def preparation : Cmd 8 41 := .seq boot (.seq Scalar.command finishCommand)

def preparationBudget (t inputWidth : ℕ) : ℕ :=
  2001*(t+inputWidth+2)^2 + 500000*(t+(2*t+inputWidth)+1)^3 +
    finishBudget t (SubexpLiftRing.baseWidth 3 t) (2*t+inputWidth)

theorem preparationBudget_polynomial (t inputWidth : ℕ) :
    preparationBudget t inputWidth ≤ 100000000*(t+inputWidth+2)^4 := by
  simp only [preparationBudget,finishBudget,Scan.tableBudget,Scan.scanBudget,
    RingProgram.ternary_baseWidth]
  nlinarith [Nat.zero_le (t^4),Nat.zero_le (t^3*inputWidth),
    Nat.zero_le (t^2*inputWidth^2),Nat.zero_le (t*inputWidth^3),Nat.zero_le (inputWidth^4),
    Nat.zero_le (t^3),Nat.zero_le (t^2*inputWidth),Nat.zero_le (t*inputWidth^2),
    Nat.zero_le (inputWidth^3),Nat.zero_le (t^2),Nat.zero_le (t*inputWidth),
    Nat.zero_le (inputWidth^2)]

structure Ready (t inputWidth : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) (d : Data) : Prop where
  encoded : IdempotentProgram.RegistersEncoded M.bits (List.replicate (2*t) true) cache.zero.val
    (RingTriple.tableEncoding (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))
    (List.replicate (3*t) true)
    (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
    (initialRegisters t M cache u) d
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  inverse : (2 : ZMod (3^t))*wordValue 3 t u=1
  counter : CounterPrograms.value (d.stacks 39)=Nat.clog 2 t
  counterLength : (d.stacks 39).length ≤ inputWidth + 1
  loopScratch : d.stacks 40=[]

theorem preparation_eval (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ n e, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      Eval preparation n (inputData bits) e ∧ Ready t bits.length M cache u e ∧
        n ≤ preparationBudget t bits.length := by
  obtain ⟨M,logword,nb,rb,hlog,hlen,hnb,heb⟩ := boot_eval bits t hv ht
  let a : Data := ⟨rb,bootStacks t bits M.bits logword⟩
  let W := 2*t+bits.length
  have hshape : (List.replicate (2*t) true).length=SubexpLiftRing.baseWidth 3 t := by
    simp [RingProgram.ternary_baseWidth]
  have hrest : Scalar.Rest a M.bits := by
    constructor
    · intro i; fin_cases i <;> simp [a,Scalar.low,bootStacks]
    · simp [a,bootStacks]
  have hslots : ∀ i, (a.stacks (Scalar.port i)).length ≤ W := by
    intro i
    fin_cases i <;> simp [a,Scalar.port,bootStacks,W]
  obtain ⟨ns,b,cache,u,hes,hp,hframe,hns⟩ := Scalar.command_prepares t ht M
    (List.replicate (2*t) true) hshape a W hrest
    (by simp [a,bootStacks]) (by simp [W]) hslots
    (by simp [a,bootStacks]) (by simp [a,bootStacks])
  have frame : ∀ j, (∀ i, Scalar.port i≠j) → b.stacks j=bootStacks t bits M.bits logword j :=
    hframe
  have h12 : b.stacks 12=List.replicate (2*t) true := by
    rw [frame 12 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have h37 : b.stacks 37=List.replicate (3*t) true := by
    rw [frame 37 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have h39 : b.stacks 39=logword := by
    rw [frame 39 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have empty : ∀ p ∈ ([22,26,32,33,34,35,36] : List (Fin 41)), b.stacks p=[] := by
    intro p hmem
    have hf : ∀ i, Scalar.port i≠p := by
      intro i he
      rw [←he] at hmem
      fin_cases i <;> simp [Scalar.port] at hmem
    rw [frame p hf]
    fin_cases p <;> simp_all [bootStacks]
  have hW : ∀ p ∈ preparationDiscard, (b.stacks p).length ≤ W := by
    intro p hmem
    by_cases hport : ∃ i, Scalar.port i=p
    · obtain ⟨i,rfl⟩ := hport
      have hb := prepared_pool_length t M cache u b hp i
      rw [RingProgram.ternary_baseWidth] at hb
      dsimp [W]; omega
    · rw [frame p (by intro i he; exact hport ⟨i,he⟩)]
      by_cases h31 : p = 31
      · subst p
        simp [bootStacks, W]
      by_cases h29 : p = 29
      · subst p
        simp [bootStacks, W] ; omega
      have h5 : p ≠ 5 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h12 : p ≠ 12 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h37 : p ≠ 37 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h39 : p ≠ 39 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      simp [bootStacks, h31, h29, h5, h12, h37, h39]
  obtain ⟨nf,e,hnf,hef,hfinished⟩ := finishCommand_eval t ht M cache u b hp W h37
    (empty 26 (by simp)) (empty 22 (by simp)) (empty 32 (by simp))
    (empty 33 (by simp)) (empty 34 (by simp)) (empty 35 (by simp)) (empty 36 (by simp)) hW
  have enc := finished_encoded t ht M cache u b e hp h12 h37 hfinished
  have hcounter := finished_counter t b e _ hfinished
  refine ⟨nb+(ns+nf),e,M,cache,u,heb.seq (hes.seq hef),?_,?_⟩
  · refine ⟨enc,hp.zeroCanonical,hp.inverse,?_,?_,hcounter.2⟩
    · simpa [hcounter.1,h39] using hlog
    · simpa [hcounter.1,h39] using hlen
  · have hs := Scalar.budget_polynomial t W
    dsimp [preparationBudget,W] at *
    omega

def program := compiled preparation 31 32

theorem program_runs (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ e : Data, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      RunsIn program (preparationBudget t bits.length+1)
        ((inputData bits).withPC (some program.entry)) (e.withPC none) ∧
      Ready t bits.length M cache u e := by
  obtain ⟨n,e,M,cache,u,he,ready,hn⟩ := preparation_eval bits t hv ht
  exact ⟨e,M,cache,u,⟨n+1,by omega,compiled_halt_trace he 31 32⟩,ready⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
