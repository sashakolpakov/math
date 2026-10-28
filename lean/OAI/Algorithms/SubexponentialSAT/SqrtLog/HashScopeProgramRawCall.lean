import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramFromTuple
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawFrame

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 11 49

def data (rf : Fin 11 → Bool)
    (raw width modulus master shape scopeWire source pay out tmp : List Bool) : Data :=
  ⟨rf,fun i => if i=0 then raw else if i=1 then width else if i=7 then modulus
    else if i=14 then master else if i=15 then shape else if i=16 then scopeWire
    else if i=45 then tmp else if i=46 then source else if i=47 then pay
    else if i=48 then out else []⟩

def zeroRegs : Fin 11 → Bool := fun _ => false


def callStacks : Fin 46 → Fin 49 := Fin.castAdd 3
theorem callStacks_injective : Function.Injective callStacks := Fin.castAdd_injective _ _
abbrev call : Cmd 11 49 := .call (ProgramLinking.liftProgram FromTuple.program id callStacks)

theorem call_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape source out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ FromTuple.cost t d b modulus clauses codes terms, ∃ rf,
      Eval call n
        (data zeroRegs (rowBits b terms).reverse width modulus
          (Encoding.encodeList id clauses) shape [] source [] out [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (scopeBytes (clauses := clauses) t d codes terms) source [] out []) := by
  obtain ⟨rf,h⟩ := FromTuple.state_runsIn t d ht b hb clauses codes hc terms hbound
    (fun _ => false) width modulus shape hw hm hshape
  let a := data zeroRegs (rowBits b terms).reverse width modulus
    (Encoding.encodeList id clauses) shape [] source [] out []
  let z := FromTuple.finished rf width modulus (Encoding.encodeList id clauses) shape
    (scopeBytes (clauses := clauses) t d codes terms)
  have ha : restrictState id callStacks a=FromTuple.extend
      (HashInputProgram.Loop.data (fun _ => false) (HashInputProgram.Loop.rawInput b terms)
        width modulus (Encoding.encodeList id clauses) shape [] [] [] [] []) := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨n,hn,he⟩ := lifted_call FromTuple.program id callStacks Function.injective_id
    callStacks_injective a z (FromTuple.cost t d b modulus clauses codes terms)
    (by simpa [ha,z,scopeBytes] using h)
  have hz : embedState id callStacks a z=
      data rf [] width modulus (Encoding.encodeList id clauses) shape
        (scopeBytes (clauses := clauses) t d codes terms) source [] out [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id callStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,h.symm⟩
      have h7 : i≠7 := fun h => hi ⟨7,h.symm⟩
      have h14 : i≠14 := fun h => hi ⟨14,h.symm⟩
      have h15 : i≠15 := fun h => hi ⟨15,h.symm⟩
      have h16 : i≠16 := fun h => hi ⟨16,h.symm⟩
      have h45 : i≠45 := fun h => hi ⟨45,h.symm⟩
      simp [a,data,h0,h1,h7,h14,h15,h16,h45]
  exact ⟨n,hn,rf,by simpa [call,hz] using he⟩

abbrev takeInput : Cmd 11 49 := .seq (.call (StackRoutines.transferProgram 47 45 8 9))
  (.call (StackRoutines.transferProgram 45 0 8 9))

theorem takeInput_eval (rf : Fin 11 → Bool) (width modulus master shape source bits out : List Bool) :
    Eval takeInput (6*bits.length+6)
      (data rf [] width modulus master shape [] source bits.reverse out [])
      (data (readRegs (readRegs rf 8 9 none) 8 9 none) bits.reverse width modulus master shape [] source [] out []) := by
  let a := data rf [] width modulus master shape [] source bits.reverse out []
  let z := SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 47 45 8 9
  have h1 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 47 45 8 9 (by decide) (by decide)
  have h2 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval z 45 0 8 9 (by decide) (by decide)
  have hz : (z.stacks 45).length=bits.length := by
    simp [z,a,data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer z 45 0 8 9=
      data (readRegs (readRegs rf 8 9 none) 8 9 none) bits.reverse width modulus master shape [] source [] out [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [z,a,data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]
  have hh := h1.seq h2
  rw [hz,he] at hh
  simpa [takeInput,a,data,show 3*bits.length+3+(3*bits.length+3)=6*bits.length+6 by omega] using hh

abbrev takeOutput : Cmd 11 49 := .call (StackRoutines.transferProgram 16 47 8 9)

theorem takeOutput_eval (rf : Fin 11 → Bool) (width modulus master shape source bits out : List Bool) :
    Eval takeOutput (3*bits.length+3)
      (data rf [] width modulus master shape bits source [] out [])
      (data (readRegs rf 8 9 none) [] width modulus master shape [] source bits.reverse out []) := by
  have hh := SubexponentialSAT.SubexpScanPrimitives.transfer_eval
    (data rf [] width modulus master shape bits source [] out []) 16 47 8 9 (by decide) (by decide)
  convert hh using 1
  · rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext i; fin_cases i <;> simp [data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]

abbrev callback : Cmd 11 49 := .seq takeInput (.seq Reset.all (.seq call (.seq takeOutput RawFrame.command)))

def callbackCost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  6*(rowBits b terms).length+FromTuple.cost t d b modulus clauses codes terms+
    8*(scopeBytes (clauses := clauses) t d codes terms).length+30

theorem callback_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape source out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ callbackCost t d b modulus clauses codes terms, ∃ rf',
      rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval callback n
        (data rf [] width modulus (Encoding.encodeList id clauses) shape [] source (rowBits b terms).reverse out [])
        (data rf' [] width modulus (Encoding.encodeList id clauses) shape [] source []
          (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) out) []) := by
  have hi := takeInput_eval rf width modulus (Encoding.encodeList id clauses) shape source (rowBits b terms) out
  have hz := Reset.all_eval (data (readRegs (readRegs rf 8 9 none) 8 9 none)
    (rowBits b terms).reverse width modulus (Encoding.encodeList id clauses) shape [] source [] out [])
  obtain ⟨nc,hnc,rc,hec⟩ := call_eval t d ht b hb clauses codes hc terms hbound width modulus shape source out hw hm hshape
  have ho := takeOutput_eval rc width modulus (Encoding.encodeList id clauses) shape source (scopeBytes (clauses := clauses) t d codes terms) out
  let a := data (readRegs rc 8 9 none) [] width modulus (Encoding.encodeList id clauses) shape [] source
    (scopeBytes (clauses := clauses) t d codes terms).reverse out []
  obtain ⟨z,he,h47,h48,h8,h9,h10,hframe⟩ := RawFrame.command_eval a (scopeBytes (clauses := clauses) t d codes terms) (by simp [a,data])
  have hez : z=data z.regs [] width modulus (Encoding.encodeList id clauses) shape [] source []
      (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) out) [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      by_cases hi47 : i=47
      · subst i; simpa [data] using h47
      by_cases hi48 : i=48
      · subst i; simpa [a,data] using h48
      rw [hframe i hi47 hi48]
      simp [a,data,hi47,hi48]
  rw [hez] at he
  refine ⟨_,?_,z.regs,h8,h9,h10,hi.seq (hz.seq (hec.seq (ho.seq he)))⟩
  unfold callbackCost
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
