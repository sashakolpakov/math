import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNumeratorRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramIntegerFinish

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 10 64
abbrev Saved := LayoutProgramScalar.FromCounts.Saved

variable {r Q : ℕ}

abbrev good : Cmd 10 64 := .seq Numerator.command (.seq TypeCompare.command IntegerFinish.command)
abbrev command : Cmd 10 64 := .seq guard (.ite 9 good (.base .skip))
def program := compiled command 23 53

def output (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q) (u y : UniversalType r Q 1)
    (result : WordPair) : Data :=
  ⟨regs,Function.update (Function.update
    (Numerator.state c regs t u y [] [] ([],[])).stacks 53 result.1) 54 result.2⟩

def value (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℤ :=
  if anchorValid (0 : Fin 1) t u y then
    (if u=y then (2:ℤ)^(R-1) else 0)-LayoutCoefficientAlgorithm.scalarEntry (0:Fin 1) t A R u y
  else 0

def lengthBound (R W P : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  (R-(MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)-1))*
    LayoutProgramScalar.termGrowth (2*W+P)

def budget (A R W P D : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℕ :=
  guardStageCost r Q 1 0 t.val+Numerator.budget A R W P t u y+
    27*CollisionProgram.typeWidth r Q 1+9*lengthBound R W P u y+
    100*(lengthBound R W P u y+D+1)^2+60

theorem output_empty (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q) (u y : UniversalType r Q 1) :
    output c regs t u y ([],[]) = Numerator.state c regs t u y [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases h53 : j=53 <;> by_cases h54 : j=54 <;>
    simp [Numerator.state,Numerator.baseStacks,Function.update_apply,h53,h54]

theorem command_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ budget a.length R width.length (pairLength power) power.1.length t u y,
      ∃ rf result, Eval command n (Numerator.state c regs t u y [] [] ([],[]))
        (output c rf t u y result) ∧
      pairValue result=value a.length R t u y ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧
      pairLength result ≤ lengthBound R width.length (pairLength power) u y+power.1.length+1 := by
  intro c
  obtain ⟨ng,hng,m,hg,hms,hflag⟩ := UniversalEntry.guard_eval t u y
    (Numerator.state c regs t u y [] [] ([],[])) (Numerator.guard_project c regs t u y)
  have hm : m=Numerator.state c m.regs t u y [] [] ([],[]) :=
    congrArg₂ StructuredProgram.State.mk rfl hms
  rw [hm] at hg
  by_cases ha : anchorValid (0 : Fin 1) t u y
  · have h9 : (Numerator.state c m.regs t u y [] [] ([],[])).regs 9=true := by
      simpa [Numerator.state,ha] using hflag
    obtain ⟨nn,hnn,rn,num,hen,hvn,hmn,hln⟩ := Numerator.command_eval Hwords width power m.regs a R t u y
      hlen hwords hvalues hp hpt hwidth hAQ hQ
    let s := Numerator.state c rn t u y [] [] num
    obtain ⟨nc,hnc,z,hec,hzs,h7⟩ := TypeCompare.command_eval s
      (by simp [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input])
      (by simp [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input])
      (by simp [s,Numerator.state]) (by simp [s,Numerator.state])
    have hz : z=Numerator.state c z.regs t u y [] [] num :=
      congrArg₂ StructuredProgram.State.mk rfl hzs
    rw [hz] at hec
    have hz7 : z.regs 7=decide (u=y) := by
      simpa [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input] using h7
    let z' := Numerator.state c z.regs t u y [] [] num
    have hready : IntegerFinish.Ready z' := by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [z',Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input]
    obtain ⟨nf,hnf,e,p,n,hef,hes,hvf,hmf,hlf⟩ := IntegerFinish.command_eval z' hready
    have heout : e=output c e.regs t u y (p,n) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      rw [hes]
      funext j
      by_cases h50 : j=50 <;> by_cases h51 : j=51 <;> by_cases h53 : j=53 <;>
        by_cases h54 : j=54 <;> simp [IntegerFinish.output,z',Numerator.state,Function.update_apply,h50,h51,h53,h54]
    rw [heout] at hef
    have hrun := hg.seq (Eval.ite_true (no := .base .skip) h9 (hen.seq (hec.seq hef)))
    have hlenNum : num.1.length+num.2.length ≤ lengthBound R width.length (pairLength power) u y := hln
    have htimef : nf ≤ 9*num.1.length+2*num.2.length+100*(num.2.length+power.1.length+1)^2+19 := by
      simpa [IntegerFinish.budget,z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved] using hnf
    have htimec : nc ≤ 27*CollisionProgram.typeWidth r Q 1+34 := by
      have hc : nc ≤ 18*CollisionProgram.typeWidth r Q 1+9*CollisionProgram.typeWidth r Q 1+34 := by
        simpa [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,
          MatrixEntryProgram.input,CollisionProgram.encodeType_length] using hnc
      omega
    have hsquare : (num.2.length+power.1.length+1)^2 ≤
        (lengthBound R width.length (pairLength power) u y+power.1.length+1)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    refine ⟨ng+(nn+(nc+nf)+1),?_,e.regs,(p,n),hrun,?_,?_,?_⟩
    · unfold budget
      omega
    · simp [z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved,hz7,hpos] at hvf
      change (BinaryArithmetic.toNat num.1:ℤ)-BinaryArithmetic.toNat num.2 = _ at hvn
      simp only [Numerator.value,ite_eq_left ha] at hvn
      simpa [pairValue,RowSelectionProgram.signedValue,value,ha,hvn] using hvf
    · simp [z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved,hpos] at hmf
      change BinaryArithmetic.toNat num.1+BinaryArithmetic.toNat num.2 ≤ _ at hmn
      change BinaryArithmetic.toNat p+BinaryArithmetic.toNat n ≤ _
      unfold constraintMassBound
      split_ifs at hmf <;> omega
    · have hh : p.length+n.length ≤ num.1.length+num.2.length+power.1.length+1 := by
        simpa [z',Numerator.state,Numerator.baseStacks,c,
          LayoutProgramScalar.FromCounts.unsignedSaved] using hlf
      change p.length+n.length ≤ _
      omega
  · have h9 : (Numerator.state c m.regs t u y [] [] ([],[])).regs 9=false := by
      simpa [Numerator.state,ha] using hflag
    have ht := hg.seq (Eval.ite_false (yes := good) h9 (Eval.base (StructuredProgram.Eval.skip _)))
    rw [← output_empty c m.regs t u y] at ht
    refine ⟨ng+1,?_,m.regs,([],[]),ht,?_,?_,?_⟩
    · unfold budget; omega
    · simp [pairValue,RowSelectionProgram.signedValue,value,ha,BinaryArithmetic.toNat]
    · simp [LayoutProgramScalar.wordTotal,pairTotal]
    · simp [pairLength]

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
