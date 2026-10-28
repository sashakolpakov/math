import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarCacheCell
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgramCell
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarStep

namespace OAI.Algorithms

/-! The H cache builder followed by the shared physical fixed-width adapter.
Only the common width survives alongside the two flat output arrays. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutBinomialProgram (finalState buildFinalPorts buildFinalPorts_injective
  finalFlatten finalFlatten_eval normalizedWords normalizedWords_length
  normalizedWords_values normalizedWords_word_length flatWords_eq_flatten flatZeros_eq)

 def hFlatBuild : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram buildProgram id buildFinalPorts)

theorem hFlatBuild_eval (regs : Fin 8 → Bool) (a r width : List Bool) :
    ∃ t ≤ 12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+8,
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)),
      Eval hFlatBuild t (finalState regs a r width [] [] [])
        (finalState regs' [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] []) ∧
      xs.length=r.length ∧ xs.map BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      (∀ x ∈ xs, x.length ≤ 1+2*a.length*r.length) := by
  obtain ⟨rf,xs,⟨t,ht,he⟩,hlen,hval,hw⟩ := buildProgram_runsIn regs a r
  have hs : embedState id buildFinalPorts (finalState regs a r width [] [] [])
      (buildState regs a r []) = finalState regs a r width [] [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi; rfl
  have hf : embedState id buildFinalPorts (finalState regs a r width [] [] [])
      (buildState rf [] [] (pairEncoding (xs.map fun x => (x,[])))) =
      finalState rf [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi
      have hrange : ∀ j : Fin 20, j≠19 → j∈Set.range buildFinalPorts := by decide
      have hj : i=19 := by
        by_contra hn
        exact hi (hrange i hn)
      subst i; simp [finalState]
  have hh := eval_call_lifted buildProgram id buildFinalPorts
    (finalState regs a r width [] [] []) Function.injective_id buildFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,xs,hh,hlen,hval,hw⟩

abbrev hFlatCommand : Cmd 8 20 := .seq hFlatBuild finalFlatten
def hFlatProgram := compiled hFlatCommand 17 0

theorem hFlatProgram_runsIn (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ (regs' : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn hFlatProgram
        (12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+
          110*(r.length+1)*(width.length+(1+2*a.length*r.length)+4)+16)
        ((finalState regs a r width [] [] []).withPC (some hFlatProgram.entry))
        ((finalState regs' [] [] width [] words.flatten
          (List.replicate (r.length*width.length) false)).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words, x.length=width.length) ∧
      words.map BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  obtain ⟨tb,htb,rb,xs,hb,hlen,hval,hxs⟩ := hFlatBuild_eval regs a r width
  obtain ⟨tf,htf,rf,hf⟩ := finalFlatten_eval rb width xs (1+2*a.length*r.length) hxs
  rw [hlen] at htf
  have hvalue : (normalizedWords width xs).map BinaryArithmetic.toNat=
      (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
    rw [normalizedWords_values width xs (fun x hx => (hxs x hx).trans hw),hval]
  refine ⟨rf,normalizedWords width xs,?_,by simpa using hlen,
    normalizedWords_word_length width xs,hvalue⟩
  refine ⟨tb+tf+1,by omega,?_⟩
  have hh := compiled_halt_trace (hb.seq hf) 17 0
  simpa only [hFlatProgram,hFlatCommand,flatWords_eq_flatten,flatZeros_eq,hlen] using hh

def hZeroWords (R W : ℕ) : List (List Bool) := List.replicate R (List.replicate W false)

@[simp] theorem hZeroWords_length (R W : ℕ) : (hZeroWords R W).length=R := by
  simp [hZeroWords]

theorem hZeroWords_word_length (R W : ℕ) : ∀ x∈hZeroWords R W, x.length=W := by
  intro x hx
  rcases List.mem_replicate.mp hx with ⟨_,rfl⟩
  simp

theorem hZeroWords_flatten (R W : ℕ) :
    (hZeroWords R W).flatten = List.replicate (R*W) false := by
  induction R with
  | zero => simp [hZeroWords]
  | succ R ih =>
    change List.replicate W false ++ (hZeroWords R W).flatten =
      List.replicate ((R+1)*W) false
    rw [ih,← List.replicate_add]
    congr 1
    ring

theorem zeroBits_value (W : ℕ) : BinaryArithmetic.toNat (List.replicate W false)=0 := by
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ,BinaryArithmetic.bitVal,ih]

/-- Per-entry H cache contracts used by the numerator's `Cache.Values` and
`Cache.Totals` predicates. The negative array consists of actual zero words. -/
theorem hWords_entry (A R W : ℕ) (words : List (List Bool))
    (hlen : words.length=R)
    (hval : words.map BinaryArithmetic.toNat=
      (List.range R).map (LayoutCoefficientRecurrence.H A))
    (i : ℕ) (hi : i < R) :
    pairValue (words.getD i [],(hZeroWords R W).getD i []) =
        (LayoutCoefficientRecurrence.H A i : ℤ) ∧
      wordTotal (words.getD i [],(hZeroWords R W).getD i []) = LayoutCoefficientRecurrence.H A i := by
  have hp : i < words.length := by omega
  have hget := congrArg (fun xs : List ℕ => xs.getD i 0) hval
  have hleft : (words.map BinaryArithmetic.toNat).getD i 0 =
      BinaryArithmetic.toNat (words.getD i []) := by
    simpa only [BinaryArithmetic.toNat] using
      (List.getD_map (l:=words) (d:=[]) (n:=i) BinaryArithmetic.toNat)
  have hright : ((List.range R).map (LayoutCoefficientRecurrence.H A)).getD i 0 =
      LayoutCoefficientRecurrence.H A i := by
    simp [hi]
  rw [hleft,hright] at hget
  have hz : (hZeroWords R W).getD i [] = List.replicate W false := by
    simp [hZeroWords,hi]
  change (BinaryArithmetic.toNat (words.getD i []) : ℤ) -
      (BinaryArithmetic.toNat ((hZeroWords R W).getD i []) : ℤ) = _ ∧
    BinaryArithmetic.toNat (words.getD i []) +
      BinaryArithmetic.toNat ((hZeroWords R W).getD i []) = _
  rw [hz,zeroBits_value,hget]
  simp

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
