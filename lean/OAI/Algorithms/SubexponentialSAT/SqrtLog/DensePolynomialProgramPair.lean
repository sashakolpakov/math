import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramRingCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramCell
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPair

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := SubexponentialSAT.SubexpConvolutionControl.Data
abbrev Code := SubexponentialSAT.SubexpConvolutionControl.Code

def accumulate : Code := .call (ProgramLinking.liftProgram Cell.program id lowPort)
def command : Code := .seq RingCall.command (.seq moveProduct accumulate)
def budget (degree B I : ℕ) : ℕ :=
  RingCall.budget B degree + (6*(degree*B)+6) + (Cell.eventBudget degree B I+1)

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

structure Ready (s : Store) (a b c : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  high : ∀ i, s (RingCall.ports i) =
    (RingScan.serviceState (fun _ => false) M.bits [] (RingProgram.flat a)
      (RingProgram.flat b) [] scalarWidth cache.zero.val (RingTriple.tableEncoding table)).stacks i
  low : ∀ i : Fin 20, s (lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)) =
    (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i
  array : s 102 = earlier.flatten ++ (RingProgram.flat c ++ rest)
  index : s 103 = indexWord
  indexLength : indexWord.length = earlier.length
  width : s 104 = widthWord
  widthLength : widthWord.length = degree * baseWidth p t
  rows : ∀ row ∈ earlier, row.length = widthWord.length
  scalarWidthLength : scalarWidth.length = baseWidth p t
  degreeLength : (s 204).length = degree
  scratch : s 120 = []
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → s j = []

/-- This is the concrete bit-command execution for one pair; all coefficient
arithmetic calls are the native programs, never abstract ring operations. -/
theorem command_run (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (a b c : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p t M cache table s a b c earlier rest widthWord indexWord scalarWidth frame) :
    ExecutesIn command (budget degree (baseWidth p t) indexWord.length) s
      (Function.update (Function.update (Function.update s 198 []) 199 []) 102
        (earlier.flatten ++ (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest))) := by
  intro regs
  let product := (ops.mulRun a b).1
  obtain ⟨n1,r1,hn1,he1⟩ := RingCall.command_run p t M cache hz table a b s scalarWidth
    H.degreeLength H.scalarWidthLength H.scratch H.high regs
  rw [← hmul] at he1
  let d1 : Data := ⟨r1,Function.update (Function.update (Function.update s 198 []) 199 [])
    200 (RingProgram.flat product)⟩
  let d2 := moveOut d1
  have h8 : s 8 = [] := H.low 8
  have h200 : s 200 = [] := H.high 0
  have h18 : d1.stacks 8 = [] := by simp [d1,h8]
  have h119 : d1.stacks 119 = [] := by simpa [d1] using H.work 119 (by decide) (by decide)
  have he2 := moveProduct_eval d1 h18 h119
  have hlen : (d1.stacks 200).length = degree * baseWidth p t := by simp [d1]
  have hf (j : Fin 128) (hj : j ≠ 8) : (lowState d2).stacks j = s (lowPort j) := by
    have h8j : lowPort j ≠ 8 := fun h => hj (lowPort_injective h)
    have hv : (lowPort j).val < 128 := j.isLt
    have h198 : lowPort j ≠ 198 := by intro h; rw [h] at hv; norm_num at hv
    have h199 : lowPort j ≠ 199 := by intro h; rw [h] at hv; norm_num at hv
    have h200j : lowPort j ≠ 200 := by intro h; rw [h] at hv; norm_num at hv
    simp [d2,d1,lowState,moveOut,h8j,h198,h199,h200j]
  have h102 : lowPort (102 : Fin 128) = (102 : Fin 256) := by apply Fin.ext; rfl
  have h103 : lowPort (103 : Fin 128) = (103 : Fin 256) := by apply Fin.ext; rfl
  have h104 : lowPort (104 : Fin 128) = (104 : Fin 256) := by apply Fin.ext; rfl
  have h112 : lowPort (112 : Fin 128) = (112 : Fin 256) := by apply Fin.ext; rfl
  have h113 : lowPort (113 : Fin 128) = (113 : Fin 256) := by apply Fin.ext; rfl
  have h114 : lowPort (114 : Fin 128) = (114 : Fin 256) := by apply Fin.ext; rfl
  have h115 : lowPort (115 : Fin 128) = (115 : Fin 256) := by apply Fin.ext; rfl
  have h116 : lowPort (116 : Fin 128) = (116 : Fin 256) := by apply Fin.ext; rfl
  have h117 : lowPort (117 : Fin 128) = (117 : Fin 256) := by apply Fin.ext; rfl
  have h118 : lowPort (118 : Fin 128) = (118 : Fin 256) := by apply Fin.ext; rfl
  have hsmall : ∀ i : Fin 20, (lowState d2).stacks (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i) =
      (DensePolynomialLoop.ready ((lowState d2).regs ∘ SubexponentialSAT.SubexpJetCellProgram.regPorts)
        M.bits (RingProgram.flat product) [] scalarWidth [] frame).stacks i := by
    intro i
    have hi := H.low i
    fin_cases i <;> simp [d2,d1,lowState,moveOut,lowPort,SubexponentialSAT.SubexpJetCellProgram.scalarPorts,
      DensePolynomialLoop.ready,DensePolynomialLoop.state,DensePolynomialLoop.stackArray,
      Fin.addCases] at hi ⊢ <;> exact hi
  obtain ⟨n3,hn3,e3,he3,hs3,hr3⟩ := Cell.updateCell_eval p t M cache hB ops hadd
    (lowState d2) product c earlier rest widthWord indexWord scalarWidth frame
    (by simpa only [hf 102 (by decide), h102] using H.array)
    (by simpa only [hf 103 (by decide), h103] using H.index) H.indexLength
    (by simpa only [hf 104 (by decide), h104] using H.width) H.widthLength H.rows
    H.scalarWidthLength hsmall
    (by simpa only [hf 112 (by decide), h112] using H.work 112 (by decide) (by decide))
    (by simpa only [hf 113 (by decide), h113] using H.work 113 (by decide) (by decide))
    (by simpa only [hf 114 (by decide), h114] using H.work 114 (by decide) (by decide))
    (by simpa only [hf 115 (by decide), h115] using H.work 115 (by decide) (by decide))
    (by simpa only [hf 116 (by decide), h116] using H.work 116 (by decide) (by decide))
    (by simpa only [hf 117 (by decide), h117] using H.work 117 (by decide) (by decide))
    (by simpa only [hf 118 (by decide), h118] using H.work 118 (by decide) (by decide))
  let record := earlier.flatten ++ (RingProgram.flat (ops.addRun product c).1 ++ rest)
  have hcall := eval_call_lifted Cell.program id lowPort d2
    Function.injective_id lowPort_injective
    (a := lowState d2) (b := e3) (compiled_halt_trace he3 8 102)
  rw [embed_low_input, embed_low_output d2 e3 record hs3] at hcall
  have hlast : Function.update (Function.update d2.stacks (lowPort 8) []) (lowPort 102) record =
      Function.update (Function.update (Function.update s 198 []) 199 []) 102 record := by
    funext j
    by_cases hj8 : j = 8 <;> by_cases hj200 : j = 200 <;>
      simp [d2,d1,moveOut,lowPort,Function.update_apply,hj8,hj200,h8,h200]
  rw [hlast] at hcall
  refine ⟨n1+((6*(d1.stacks 200).length+6)+(n3+1)), e3.regs, ?_, he1.seq (he2.seq hcall)⟩
  rw [hlen]
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
