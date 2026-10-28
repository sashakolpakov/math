import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgramInterface

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev NumeratorData := State 9 25

def numeratorState (c : Cache) (regs : Fin 9 → Bool)
    (counter parity queue : List Bool) (result : WordPair) : NumeratorData :=
  ⟨regs,![c.Hpositive.flatten,c.Hnegative.flatten,c.Bpositive.flatten,c.Bnegative.flatten,
    c.width,c.power.1,c.power.2,counter,[],[],[],[],[],[],[],[],[],[],queue,parity,
    [],[],[],result.1,result.2]⟩

def numeratorPreparePorts : Fin 20 → Fin 25 := Fin.castAdd 5
def numeratorScalarRegisters : Fin 8 → Fin 9 := Fin.castAdd 1
def numeratorScalarPorts : Fin 18 → Fin 25 :=
  ![7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,18,23,24]

theorem numeratorPreparePorts_injective : Function.Injective numeratorPreparePorts :=
  Fin.castAdd_injective _ _
theorem numeratorScalarRegisters_injective : Function.Injective numeratorScalarRegisters :=
  Fin.castAdd_injective _ _
theorem numeratorScalarPorts_injective : Function.Injective numeratorScalarPorts := by decide

abbrev numeratorPrepare : Cmd 9 25 :=
  .call (ProgramLinking.liftProgram prepareProgram id numeratorPreparePorts)
abbrev numeratorFold : Cmd 9 25 :=
  .call (ProgramLinking.liftProgram scalarProgram numeratorScalarRegisters numeratorScalarPorts)
abbrev numeratorCommand : Cmd 9 25 := .seq numeratorPrepare numeratorFold
def numeratorProgram := compiled numeratorCommand 7 23

def numeratorPrepareCost (N A W P : ℕ) : ℕ :=
  9*N+3*A+N*(N*(28*W+34)+140*W+18*P+222)+3*(N*(8*W+2*P+9))+24

def numeratorFoldCost (N W P : ℕ) : ℕ :=
  200000000*(N+1)*(N*termGrowth (2*W+P)+(2*W+P)+4)^2+1

private theorem numeratorPrepare_embed (c : Cache) (regs r : Fin 9 → Bool)
    (counter parity queue : List Bool) :
    embedState id numeratorPreparePorts (numeratorState c regs counter parity [] ([],[]))
      (cacheState c r [] [] [] [] queue []) = numeratorState c r [] [] queue ([],[]) := by
  apply embedState_eq_of_ports id numeratorPreparePorts _ _ _
    Function.injective_id numeratorPreparePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> simp [numeratorState,cacheState,numeratorPreparePorts]
  · intro i hi
    have hv : 20 ≤ i.val := by
      by_contra h
      exact hi ⟨⟨i.val,by omega⟩,Fin.ext rfl⟩
    fin_cases i <;> simp_all [numeratorState]

private theorem numeratorPrepare_project (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) :
    projectState id numeratorPreparePorts (numeratorState c regs counter parity [] ([],[])) =
      cacheState c regs counter [] [] [] [] parity := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [numeratorState,numeratorPreparePorts]

private theorem numeratorFold_project (c : Cache) (regs : Fin 9 → Bool) (queue : List Bool) :
    projectState numeratorScalarRegisters numeratorScalarPorts
      (numeratorState c regs [] [] queue ([],[])) =
      state (regs ∘ numeratorScalarRegisters) ([],[]) ([],[]) ([],[]) queue := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [numeratorState,numeratorScalarPorts]

private theorem numeratorFold_embed (c : Cache) (regs : Fin 9 → Bool)
    (r : Fin 8 → Bool) (queue : List Bool) (result : WordPair) :
    ∃ rout, embedState numeratorScalarRegisters numeratorScalarPorts
      (numeratorState c regs [] [] queue ([],[])) (state r result ([],[]) ([],[]) []) =
      numeratorState c rout [] [] [] result := by
  let frame := numeratorState c regs [] [] queue ([],[])
  let e := embedState numeratorScalarRegisters numeratorScalarPorts frame
    (state r result ([],[]) ([],[]) [])
  refine ⟨e.regs,?_⟩
  apply embedState_eq_of_ports numeratorScalarRegisters numeratorScalarPorts _ _ _
    numeratorScalarRegisters_injective numeratorScalarPorts_injective
  · intro i
    exact embedState_register numeratorScalarRegisters numeratorScalarPorts frame
      (state r result ([],[]) ([],[]) []) numeratorScalarRegisters_injective i
  · intro i hi
    exact embedState_register_frame numeratorScalarRegisters numeratorScalarPorts frame
      (state r result ([],[]) ([],[]) []) i hi
  · intro i; fin_cases i <;> simp [numeratorState,state,numeratorScalarPorts]
  · intro i hi
    have hrange : ∀ j : Fin 25, 7 ≤ j.val → j ∈ Set.range numeratorScalarPorts := by decide
    have hv : i.val < 7 := by
      by_contra h
      exact hi (hrange i (by omega))
    fin_cases i <;> simp_all [numeratorState]

/-- Cached numerator endpoint. The cache-value and total invariants are input
representation predicates discharged by the concrete cache builders. -/
theorem numeratorProgram_runsIn (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) (A R d h Q : ℕ)
    (hc : counter.length = R-d) (ha : parity.length = A)
    (hu : c.Uniform) (hf : c.Fits (R-d))
    (hv : c.Values A R h) (hm : c.Totals A R h)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
    ∃ r result,
      RunsIn numeratorProgram
        (numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
          numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1)
        ((numeratorState c regs counter parity [] ([],[])).withPC
          (some numeratorProgram.entry))
        ((numeratorState c r [] [] [] result).withPC none) ∧
      pairValue result = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power) := by
  obtain ⟨rp,xs,⟨tp,htp,hprep⟩,hx,_,hb,hvalue,hmass⟩ :=
    prepareProgram_factored_runsIn c regs counter parity A R d h hc ha hu hf hv hm
  have hp := eval_call_from_state prepareProgram id numeratorPreparePorts
    (numeratorState c regs counter parity [] ([],[])) Function.injective_id
    numeratorPreparePorts_injective (by
      simpa only [numeratorPrepare_project] using hprep)
  rw [numeratorPrepare_embed] at hp
  obtain ⟨rf,result,⟨tf,htf,hfold⟩,hval,htotal,hlen⟩ :=
    scalarProgram_runsIn_total xs (rp ∘ numeratorScalarRegisters) ([],[]) 0
      (2*c.width.length+pairLength c.power) (by rfl) hb
  have hs := eval_call_from_state scalarProgram numeratorScalarRegisters numeratorScalarPorts
    (numeratorState c rp [] [] (pairEncoding (tripleWords xs)) ([],[]))
    numeratorScalarRegisters_injective numeratorScalarPorts_injective (by
      simpa only [numeratorFold_project] using hfold)
  obtain ⟨r,he⟩ := numeratorFold_embed c rp rf (pairEncoding (tripleWords xs)) result
  rw [he] at hs
  refine ⟨r,result,⟨tp+tf+1,?_,compiled_halt_trace (hp.seq hs) 7 23⟩,?_,?_,?_⟩
  · have hlenx : xs.length = R-d := hx.1
    simp only [hlenx,Nat.zero_add] at htf
    change tp ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power) at htp
    change tf ≤ numeratorFoldCost (R-d) c.width.length (pairLength c.power) at htf
    omega
  · simpa only [show pairValue ([],[]) = 0 from rfl,zero_add,hvalue] using hval
  · have hcMass : ∀ j < R,
        (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs ≤ (4*Q)^R := by
      intro j _
      rw [LayoutCoefficientAlgorithm.coefficientAt_eq]
      exact LayoutCoefficientBounds.natAbs_extend_parityCoefficients_le A R Q j hAQ hQ
    have hbound := LayoutProgram.scalarMass_le R d h Q hQ hhQ _ hcMass
    rw [← hmass] at hbound
    have ht : wordTotal result = (xs.map termTotal).sum := by
      simpa only [show wordTotal ([],[]) = 0 from rfl,zero_add] using htotal
    exact ht.trans_le hbound
  · simpa only [Nat.zero_add,hx.1] using hlen

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
