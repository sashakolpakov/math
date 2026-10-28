import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSingle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramReset
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramFrame

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Outer
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 11 25

def zeroRegs : Fin 11 → Bool := fun _ => false

def data (rf : Fin 11 → Bool) (ell row source payload out : List Bool) : Data :=
  ⟨rf,fun i => if i=18 then ell else if i=19 then row else if i=22 then source
    else if i=23 then payload else if i=24 then out else []⟩

def singleStacks (i : Fin 22) : Fin 25 := Fin.castAdd 3 i
theorem singleStacks_injective : Function.Injective singleStacks := Fin.castAdd_injective 22 3

abbrev single : Cmd 11 25 := .call (ProgramLinking.liftProgram Single.program id singleStacks)

theorem single_eval (terms : List Term) (source out : List Bool) :
    ∃ t ≤ Single.cost terms, ∃ rf,
      Eval single t (data zeroRegs [] (Encoding.encodeList payload terms) source [] out)
        (data rf [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) source [] out) := by
  obtain ⟨rf,ht⟩ := Single.program_runsIn terms
  let a := data zeroRegs [] (Encoding.encodeList payload terms) source [] out
  let b : State 11 22 := ⟨rf,SubexponentialSAT.SubexpChunkRecordMap.tapes [true]
    (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩
  have ha : restrictState id singleStacks a =
      SubexponentialSAT.SubexpChunkRecordMap.data false false false [] (Encoding.encodeList payload terms) [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨t,hn,he⟩ := lifted_call Single.program id singleStacks Function.injective_id
    singleStacks_injective a b (Single.cost terms) (by simpa [ha,b] using ht)
  have hb : embedState id singleStacks a b =
      data rf [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) source [] out := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id singleStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h18 : i ≠ 18 := fun h => hi ⟨18,h.symm⟩
      have h19 : i ≠ 19 := fun h => hi ⟨19,h.symm⟩
      simp [data,a,h18,h19]
  exact ⟨t,hn,rf,by simpa [single,hb] using he⟩

abbrev transferInput : Cmd 11 25 := .call (StackRoutines.transferProgram 23 19 8 9)
abbrev transferOutput : Cmd 11 25 := .call (StackRoutines.transferProgram 19 23 8 9)
abbrev clearEll : Cmd 11 25 := .call (StackRoutines.clearProgram 18 8 9)

theorem transferInput_eval (rf : Fin 11 → Bool) (source bits out : List Bool) :
    Eval transferInput (3*bits.length+3) (data rf [] [] source bits.reverse out)
      (data (readRegs rf 8 9 none) [] bits source [] out) := by
  have h := SubexponentialSAT.SubexpScanPrimitives.transfer_eval (data rf [] [] source bits.reverse out)
    23 19 8 9 (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [SubexponentialSAT.SubexpScanPrimitives.afterTransfer,data,StackRoutines.transferStacks]

theorem reset_eval (rf : Fin 11 → Bool) (row source out : List Bool) :
    Eval (Reset.all : Cmd 11 25) 11 (data rf [] row source [] out)
      (data zeroRegs [] row source [] out) := Reset.all_eval _

theorem transferOutput_eval (rf : Fin 11 → Bool) (ell row source out : List Bool) :
    Eval transferOutput (3*row.length+3) (data rf ell row source [] out)
      (data (readRegs rf 8 9 none) ell [] source row.reverse out) := by
  have h := SubexponentialSAT.SubexpScanPrimitives.transfer_eval (data rf ell row source [] out)
    19 23 8 9 (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [SubexponentialSAT.SubexpScanPrimitives.afterTransfer,data,StackRoutines.transferStacks]

theorem clearEll_eval (rf : Fin 11 → Bool) (source p out : List Bool) :
    Eval clearEll 5 (data rf [true] [] source p out)
      (data (readRegs rf 8 9 none) [] [] source p out) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (18 : Fin 25) (8 : Fin 11) 9
    (data rf [true] [] source p out)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,StackRoutines.clearStacks]

abbrev callback : Cmd 11 25 := .seq transferInput (.seq Reset.all (.seq single
  (.seq transferOutput (.seq clearEll Frame.command))))

def callbackCost (terms : List Term) : ℕ :=
  3*(Encoding.encodeList payload terms).length + Single.cost terms +
    8*(Encoding.encodeList Encoding.encodeNat (scope terms)).length+32

theorem callback_eval (terms : List Term) (rf : Fin 11 → Bool) (source out : List Bool) :
    ∃ t ≤ callbackCost terms, ∃ rf', rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval callback t (data rf [] [] source (Encoding.encodeList payload terms).reverse out)
        (data rf' [] [] source []
          (SubexponentialSAT.Subexp.TupleProgram.prependRecord (Encoding.encodeList Encoding.encodeNat (scope terms)) out)) := by
  let bits := Encoding.encodeList payload terms
  let scopeWire := Encoding.encodeList Encoding.encodeNat (scope terms)
  have hi := transferInput_eval rf source bits out
  have hz := reset_eval (readRegs rf 8 9 none) bits source out
  obtain ⟨ts,hs,rs,hes⟩ := single_eval terms source out
  have ho := transferOutput_eval rs [true] scopeWire source out
  have hc := clearEll_eval (readRegs rs 8 9 none) source scopeWire.reverse out
  let a := data (readRegs (readRegs rs 8 9 none) 8 9 none) [] [] source scopeWire.reverse out
  obtain ⟨b,he,h23,h24,h8,h9,h10,hframe⟩ := Frame.command_eval a scopeWire (by simp [a,data])
  have hb : b = data b.regs [] [] source [] (SubexponentialSAT.Subexp.TupleProgram.prependRecord scopeWire out) := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      by_cases h23i : i=23
      · subst i; simpa [data] using h23
      by_cases h24i : i=24
      · subst i; simpa [a,data] using h24
      rw [hframe i h23i h24i]
      simp [a,data,h23i,h24i]
  rw [hb] at he
  refine ⟨_,?_,b.regs,h8,h9,h10,hi.seq (hz.seq (hes.seq (ho.seq (hc.seq he))))⟩
  unfold callbackCost
  dsimp [bits,scopeWire] at *
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Outer

end OAI.Algorithms
