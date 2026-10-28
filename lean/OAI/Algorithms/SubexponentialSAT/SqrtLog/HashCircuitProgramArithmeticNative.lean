import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramWeightedCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMemory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct

namespace OAI.Algorithms


/-! Component: HashCircuitProgramArithmetic. All public namespaces and APIs are retained. -/


/-! Native arithmetic wiring for the hash interpreter. Scale and normalized
addition are fixed imported instruction tables. Product is wired separately
when the native product table is supplied by its implementation module. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Keep the full arithmetic cache on its low ports. -/
def scalePorts : Fin 40 → Fin 96 := Fin.castAdd 56
theorem scalePorts_injective : Function.Injective scalePorts := Fin.castAdd_injective _ _

abbrev scale : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts)

/-- The normalizer's coefficient scratch17 and lookup scratch22 must not
overwrite the multiplication cache at those physical ports. -/
def addPorts (destination : Fin 96) : Fin 28 → Fin 96 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,destination,16,49,18,19,20,21,50,23,51,25,26,38]

theorem addPorts_literal_injective : Function.Injective (addPorts 61) := by decide
theorem addPorts_row_injective : Function.Injective (addPorts 68) := by decide

abbrev addTo (destination : Fin 96) : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram MomentsProgram.Normalize.program id (addPorts destination))

def arithmeticPorts : Fin 56 → Fin 96 := Fin.castAdd 40
theorem arithmeticPorts_injective : Function.Injective arithmeticPorts := Fin.castAdd_injective _ _

abbrev scalePhase : Cmd 8 96 :=
  liftCommand MomentsProgram.Product.scalePhase 41 38 id arithmeticPorts
abbrev normalizePhase : Cmd 8 96 :=
  liftCommand MomentsProgram.Product.normalizePhase 4 42 id arithmeticPorts

/-- Shared fixed weighted-sum core, retaining the low56 arithmetic ABI. -/
abbrev weightedCore : Cmd 8 96 :=
  liftCommand WeightedCore.command 41 42 id arithmeticPorts

/-- Input61 is replaced by one minus its value. -/
abbrev complement : Cmd 8 96 :=
  .seq (copy 61 41 70)
    (.seq (copy 76 44 70)
      (.seq (copy 69 42 70)
        (.seq weightedCore
          (.seq (clear 61)
            (.seq (copy 42 61 70) (.seq (clear 42) (clear 41)))))))

/-- Parsed reversed weight65 becomes forward coefficient44 through an actual
transfer. The scaled clause is accumulated with the prior row dictionary. -/
abbrev accumulate : Cmd 8 96 :=
  .seq (copy 67 41 70)
    (.seq (transfer 65 44)
      (.seq (copy 68 42 70)
        (.seq weightedCore
          (.seq (clear 67)
            (.seq (clear 68)
              (.seq (copy 42 68 70) (.seq (clear 42) (clear 41))))))))

/-- Product's local ABI isA40, B41, result42, with B preserved. The copied
operands and native result are reclaimed after moving the result to67. -/
abbrev productAdapter (product : Cmd 8 96) : Cmd 8 96 :=
  .seq (copy 67 40 70)
    (.seq (copy 61 41 70)
      (.seq product
        (.seq (clear 67)
          (.seq (clear 61)
            (.seq (copy 42 67 70) (.seq (clear 42) (clear 41)))))))

abbrev wiredArithmetic (product : Cmd 8 96) : Arithmetic :=
  ⟨complement,productAdapter product,accumulate⟩

/-- Calling the scale table retains exactly its checked primitive trace,
with all caller stacks outside0..39 framed. -/
theorem scale_call {n : ℕ} {a b : Squarefree.ScaleProgram.Data}
    (frame : Machine)
    (h : Trace Squarefree.ScaleProgram.program n
      (a.withPC (some Squarefree.ScaleProgram.program.entry)) (b.withPC none)) :
    Eval scale n (embedState id scalePorts frame a) (embedState id scalePorts frame b) :=
  eval_call_lifted Squarefree.ScaleProgram.program id scalePorts frame
    Function.injective_id scalePorts_injective h

theorem add_literal_call {n : ℕ} {a b : MomentsProgram.Normalize.Data}
    (frame : Machine)
    (h : Trace MomentsProgram.Normalize.program n
      (a.withPC (some MomentsProgram.Normalize.program.entry)) (b.withPC none)) :
    Eval (addTo 61) n (embedState id (addPorts 61) frame a)
      (embedState id (addPorts 61) frame b) :=
  eval_call_lifted MomentsProgram.Normalize.program id (addPorts 61) frame
    Function.injective_id addPorts_literal_injective h

theorem add_row_call {n : ℕ} {a b : MomentsProgram.Normalize.Data}
    (frame : Machine)
    (h : Trace MomentsProgram.Normalize.program n
      (a.withPC (some MomentsProgram.Normalize.program.entry)) (b.withPC none)) :
    Eval (addTo 68) n (embedState id (addPorts 68) frame a)
      (embedState id (addPorts 68) frame b) :=
  eval_call_lifted MomentsProgram.Normalize.program id (addPorts 68) frame
    Function.injective_id addPorts_row_injective h

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def productPorts : Fin 56 → Fin 96 := Fin.castAdd 40
theorem productPorts_injective : Function.Injective productPorts := Fin.castAdd_injective _ _

abbrev product : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram MomentsProgram.Product.program id productPorts)

def arithmetic : Arithmetic := wiredArithmetic product

abbrev command : Cmd 8 96 := rowCommand arithmetic

def program := compiled command 64 68

/-- The product subroutine is the real fixed sparse-product table. Its trace
is preserved by the call, and every caller stack above55 remains framed. -/
theorem product_call {n : ℕ} {a b : MomentsProgram.Product.Data}
    (frame : Machine)
    (h : Trace MomentsProgram.Product.program n
      (a.withPC (some MomentsProgram.Product.program.entry)) (b.withPC none)) :
    Eval product n (embedState id productPorts frame a) (embedState id productPorts frame b) :=
  eval_call_lifted MomentsProgram.Product.program id productPorts frame
    Function.injective_id productPorts_injective h

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Reversal transfer consumes a high parsed payload into the low workspace. -/
theorem transfer_high_low (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src : Fin 40) (dst : Fin 56) :
    Eval (transfer (highPort src) (lowPort dst)) (3*(high src).length+3)
      (state regs low high)
      (state (readRegs regs 0 1 none)
        (Function.update low dst ((high src).reverse ++ low dst))
        (Function.update high src [])) := by
  have h := Native.transfer_eval (state regs low high) (highPort src) (lowPort dst)
    (low_ne_high dst src).symm
  simpa only [state,transferred,StackRoutines.transferStacks,tapes_high,tapes_low,
    update_low,update_high] using h

@[simp] theorem update_product_left (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 40 w =
      MomentsProgram.Product.tapes {s with left := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_right (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 41 w =
      MomentsProgram.Product.tapes {s with right := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_acc (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 42 w =
      MomentsProgram.Product.tapes {s with acc := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_coeff (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 44 w =
      MomentsProgram.Product.tapes {s with coeff := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]

/-- Preserving copy between persistent interpreter words. -/
theorem copy_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst tmp : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : high tmp = []) :
    Eval (copy (highPort src) (highPort dst) (highPort tmp)) (7*(high src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high dst (high src ++ high dst))) := by
  have h := Native.copy_eval (state regs low high) (highPort src) (highPort dst) (highPort tmp)
    (fun he => hsd (high_injective he)) (fun he => hst (high_injective he))
    (fun he => htd (high_injective he)) (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,update_high] using h

/-- The low core's measured execution is lifted without touching high tapes. -/
theorem weightedCore_lift {cost : ℕ} {regs rr : Fin 8 → Bool}
    {a b : MomentsProgram.Product.Store} (high : Fin 40 → List Bool)
    (h : Eval WeightedCore.command cost (MomentsProgram.Product.state regs a)
      (MomentsProgram.Product.state rr b)) :
    Eval weightedCore (cost+1) (state regs (MomentsProgram.Product.tapes a) high)
      (state rr (MomentsProgram.Product.tapes b) high) := by
  have hh := eval_liftCommand h 41 42 id arithmeticPorts
    (state regs (MomentsProgram.Product.tapes a) high) Function.injective_id low_injective
  simpa only [weightedCore, MomentsProgram.Product.state,
    show arithmeticPorts = lowPort from rfl, embed_low] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Memory

variable {K : Type*} [DecidableEq K]

def complementedHigh (high : Fin 40 → List Bool) (result : List Bool) :=
  Function.update (Function.update high (5 : Fin 40) []) (5 : Fin 40) result

def accumulatedHigh (high : Fin 40 → List Bool) (result : List Bool) :=
  Function.update (Function.update (Function.update (Function.update high
    (9 : Fin 40) []) (11 : Fin 40) []) (12 : Fin 40) []) (12 : Fin 40) result

/-- A cached scalar and seed are physically copied, applied and reclaimed.
For the literal-complement use they are the represented minus-one and one. -/
theorem complement_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width uCap zCap : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 5 = Squarefree.ScaleProgram.encode key entries)
    (hc : high 20 = RingProgram.flat scalar)
    (hs : high 13 = Normalize.bytes key seed) (htmp : high 14 = []) :
    let idle := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
    ∃ cost ≤ 36*(high 5).length+18*(high 20).length+7*(high 13).length+
      9*result.length+9*degree.length+Squarefree.ScaleProgram.budget key entries+
      Normalize.work p t M cache key weighted seed+73,
      ∃ rr, Eval complement cost (Memory.state regs (Product.tapes idle) high)
        (Memory.state rr (Product.tapes idle) (complementedHigh high result)) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
  let a := Squarefree.ScaleProgram.encode key entries
  let c := RingProgram.flat scalar
  let s := Normalize.bytes key seed
  let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
  let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := Memory.copy_high_low regs (Product.tapes e) high 5 14 41 (by decide) htmp
  have hz41 : Product.tapes e 41 = [] := rfl
  simp only [ha,hz41,List.append_nil,update_product_right] at h1
  have h2 := Memory.copy_high_low r1 (Product.tapes {e with right := a}) high 20 14 44 (by decide) htmp
  have hz44 : Product.tapes {e with right := a} 44 = [] := rfl
  simp only [hc,hz44,List.append_nil,update_product_coeff] at h2
  have h3 := Memory.copy_high_low r2 (Product.tapes {e with right := a,coeff := c}) high 13 14 42 (by decide) htmp
  have hz42 : Product.tapes {e with right := a,coeff := c} 42 = [] := rfl
  simp only [hs,hz42,List.append_nil,update_product_acc] at h3
  obtain ⟨k,hkCost,r4,hcore⟩ := WeightedCore.command_eval p t M cache hz table scalar degree width hd hw
    key hk entries seed r3 {e with right := a,coeff := c,acc := s}
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h4 := weightedCore_lift high hcore
  change Eval weightedCore (k+1)
    (Memory.state r3 (Product.tapes {e with right := a,coeff := c,acc := s}) high)
    (Memory.state r4 (Product.tapes {e with right := a,acc := result}) high) at h4
  have h5 := Memory.clear_high r4 (Product.tapes {e with right := a,acc := result}) high 5
  simp only [ha] at h5
  let r5 := readRegs r4 0 1 none
  let high1 := Function.update high (5 : Fin 40) []
  have htmp1 : high1 14 = [] := by simpa [high1] using htmp
  have h6 := Memory.copy_low_high r5 (Product.tapes {e with right := a,acc := result}) high1 42 5 14 (by decide) htmp1
  have hres : Product.tapes {e with right := a,acc := result} 42 = result := rfl
  have hhigh1 : high1 5 = [] := by simp [high1]
  simp only [hres,hhigh1,List.append_nil] at h6
  let r6 := readRegs r5 0 1 none
  let high2 := Function.update high1 (5 : Fin 40) result
  have h7 := Memory.clear_low r6 (Product.tapes {e with right := a,acc := result}) high2 42
  simp only [hres,update_product_acc] at h7
  let r7 := readRegs r6 0 1 none
  have h8 := Memory.clear_low r7 (Product.tapes {e with right := a,acc := []}) high2 41
  have hra : Product.tapes {e with right := a,acc := []} 41 = a := rfl
  simp only [hra,update_product_right] at h8
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨11*a.length+7*c.length+7*s.length+9*result.length+k+30,?_,readRegs r7 0 1 none,?_⟩
  · rw [ha,hc,hs]
    dsimp only [a,c,s,e,Product.idle,weighted,result] at hkCost ⊢
    omega
  · convert hrun using 1 <;> first | rfl | (dsimp only [a,c,s,weighted,result]; omega)

/-- The row adapter consumes the reversed parsed scalar and clause dictionary,
adds the scaled clause to the prior row, and leaves all other high data intact. -/
theorem accumulate_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width uCap zCap : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11 = Squarefree.ScaleProgram.encode key entries)
    (hc : high 9 = (RingProgram.flat scalar).reverse)
    (hs : high 12 = Normalize.bytes key seed) (htmp : high 14 = []) :
    let idle := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
    ∃ cost ≤ 36*(high 11).length+14*(high 9).length+9*(high 12).length+
      9*result.length+9*degree.length+Squarefree.ScaleProgram.budget key entries+
      Normalize.work p t M cache key weighted seed+74,
      ∃ rr, Eval accumulate cost (Memory.state regs (Product.tapes idle) high)
        (Memory.state rr (Product.tapes idle) (accumulatedHigh high result)) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
  let a := Squarefree.ScaleProgram.encode key entries
  let c := RingProgram.flat scalar
  let s := Normalize.bytes key seed
  let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
  let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := Memory.copy_high_low regs (Product.tapes e) high 11 14 41 (by decide) htmp
  have hz41 : Product.tapes e 41 = [] := rfl
  simp only [ha,hz41,List.append_nil,update_product_right] at h1
  have h2 := Memory.transfer_high_low r1 (Product.tapes {e with right := a}) high 9 44
  have hz44 : Product.tapes {e with right := a} 44 = [] := rfl
  simp only [hc,List.length_reverse,List.reverse_reverse,hz44,List.append_nil,update_product_coeff] at h2
  let high0 := Function.update high (9 : Fin 40) []
  have htmp0 : high0 14 = [] := by simpa [high0] using htmp
  have hseed0 : high0 12 = s := by simpa [high0,s] using hs
  have h3 := Memory.copy_high_low r2 (Product.tapes {e with right := a,coeff := c}) high0 12 14 42 (by decide) htmp0
  have hz42 : Product.tapes {e with right := a,coeff := c} 42 = [] := rfl
  simp only [hseed0,hz42,List.append_nil,update_product_acc] at h3
  obtain ⟨k,hkCost,r4,hcore⟩ := WeightedCore.command_eval p t M cache hz table scalar degree width hd hw
    key hk entries seed r3 {e with right := a,coeff := c,acc := s}
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h4 := weightedCore_lift high0 hcore
  change Eval weightedCore (k+1)
    (Memory.state r3 (Product.tapes {e with right := a,coeff := c,acc := s}) high0)
    (Memory.state r4 (Product.tapes {e with right := a,acc := result}) high0) at h4
  have h5 := Memory.clear_high r4 (Product.tapes {e with right := a,acc := result}) high0 11
  have hhigh0 : high0 11 = a := by simpa [high0,a] using ha
  simp only [hhigh0] at h5
  let r5 := readRegs r4 0 1 none
  let high1 := Function.update high0 (11 : Fin 40) []
  have h6 := Memory.clear_high r5 (Product.tapes {e with right := a,acc := result}) high1 12
  have hhigh1 : high1 12 = s := by simpa [high1,high0,s] using hs
  simp only [hhigh1] at h6
  let r6 := readRegs r5 0 1 none
  let high2 := Function.update high1 (12 : Fin 40) []
  have htmp2 : high2 14 = [] := by simpa [high2,high1,high0] using htmp
  have h7 := Memory.copy_low_high r6 (Product.tapes {e with right := a,acc := result}) high2 42 12 14 (by decide) htmp2
  have hres : Product.tapes {e with right := a,acc := result} 42 = result := rfl
  have hhigh2 : high2 12 = [] := by simp [high2]
  simp only [hres,hhigh2,List.append_nil] at h7
  let r7 := readRegs r6 0 1 none
  let high3 := Function.update high2 (12 : Fin 40) result
  have h8 := Memory.clear_low r7 (Product.tapes {e with right := a,acc := result}) high3 42
  simp only [hres,update_product_acc] at h8
  let r8 := readRegs r7 0 1 none
  have h9 := Memory.clear_low r8 (Product.tapes {e with right := a,acc := []}) high3 41
  have hra : Product.tapes {e with right := a,acc := []} 41 = a := rfl
  simp only [hra,update_product_right] at h9
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  refine ⟨11*a.length+3*c.length+9*s.length+9*result.length+k+31,?_,readRegs r8 0 1 none,?_⟩
  · rw [ha,hc,hs,List.length_reverse]
    dsimp only [a,c,s,e,Product.idle,weighted,result] at hkCost ⊢
    omega
  · convert hrun using 1 <;> first | rfl | (dsimp only [a,c,s,weighted,result]; omega)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
namespace ProductCallback

private theorem update_left (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 40 w =
      MomentsProgram.Product.tapes {s with left := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
private theorem update_right (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 41 w =
      MomentsProgram.Product.tapes {s with right := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
private theorem update_acc (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 42 w =
      MomentsProgram.Product.tapes {s with acc := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]

def resultHigh (high : Fin 40 → List Bool) (result : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update high 11 []) 5 []) 11 result

/-- Fully native callback theorem. The only numerical assumptions specify the
actual represented coefficient ring and runtime shapes; there is no abstract
arithmetic-command or callback-cost premise. -/
theorem eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11 = MomentsProgram.Product.bytes left)
    (hb : high 5 = MomentsProgram.Product.bytes right) (htmp : high 14 = []) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    let result := MomentsProgram.Product.bytes (MomentsProgram.Product.run p t M cache table u J left right [])
    ∃ cost ≤ 9*(MomentsProgram.Product.bytes left).length +
        11*(MomentsProgram.Product.bytes right).length + 9*result.length +
        MomentsProgram.Product.work p t M cache table u J left right [] + 29,
      ∃ rr, Eval (productAdapter product) cost
        (Memory.state regs (MomentsProgram.Product.tapes e) high)
        (Memory.state rr (MomentsProgram.Product.tapes e) (resultHigh high result)) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  let a := MomentsProgram.Product.bytes left
  let b := MomentsProgram.Product.bytes right
  let result := MomentsProgram.Product.bytes (MomentsProgram.Product.run p t M cache table u J left right [])
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := Memory.copy_high_low regs (MomentsProgram.Product.tapes e) high 11 14 40 (by decide) htmp
  simp only [update_left] at h1
  have hzero40 : MomentsProgram.Product.tapes e 40 = [] := rfl
  simp only [ha,hzero40,List.append_nil] at h1
  have h2 := Memory.copy_high_low r1 (MomentsProgram.Product.tapes {e with left := a}) high
    5 14 41 (by decide) htmp
  simp only [update_right] at h2
  have hzero41 : MomentsProgram.Product.tapes {e with left := a} 41 = [] := rfl
  simp only [hb,hzero41,List.append_nil] at h2
  obtain ⟨r3,k,hk,htrace⟩ := MomentsProgram.Product.program_run p t M cache hz table degree width hd hw
    u J left right r2
  have hp := eval_call_lifted MomentsProgram.Product.program id Memory.lowPort
    (Memory.state r2 (MomentsProgram.Product.tapes {e with left := a,right := b}) high)
    Function.injective_id Memory.low_injective htrace
  simp only [MomentsProgram.Product.state,Memory.embed_low] at hp
  change Eval product k
    (Memory.state r2 (MomentsProgram.Product.tapes {e with left := a,right := b}) high)
    (Memory.state r3 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high) at hp
  have h3 := Memory.clear_high r3 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high 11
  simp only [ha] at h3
  let r4 := readRegs r3 0 1 none
  let high1 := Function.update high (11 : Fin 40) []
  have h4 := Memory.clear_high r4 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high1 5
  have hhigh1 : high1 5 = b := by simpa [high1,b] using hb
  simp only [hhigh1] at h4
  let r5 := readRegs r4 0 1 none
  let high2 := Function.update high1 (5 : Fin 40) []
  have htmp2 : high2 14 = [] := by simpa [high2,high1] using htmp
  have h5 := Memory.copy_low_high r5 (MomentsProgram.Product.tapes {e with right := b,acc := result})
    high2 42 11 14 (by decide) htmp2
  have hres : MomentsProgram.Product.tapes {e with right := b,acc := result} 42 = result := rfl
  have hhigh2 : high2 11 = [] := by simp [high2,high1]
  simp only [hres,hhigh2,List.append_nil] at h5
  let r6 := readRegs r5 0 1 none
  let high3 := Function.update high2 (11 : Fin 40) result
  have h6 := Memory.clear_low r6 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high3 42
  simp only [hres,update_acc] at h6
  let r7 := readRegs r6 0 1 none
  have h7 := Memory.clear_low r7 (MomentsProgram.Product.tapes {e with right := b,acc := []}) high3 41
  have hb41 : MomentsProgram.Product.tapes {e with right := b,acc := []} 41 = b := rfl
  simp only [hb41,update_right] at h7
  have hrun := h1.seq (h2.seq (hp.seq (h3.seq (h4.seq (h5.seq (h6.seq h7))))))
  refine ⟨9*a.length+11*b.length+9*result.length+k+27,?_,readRegs r7 0 1 none,?_⟩
  · dsimp only [a,b,result] at *
    omega
  · convert hrun using 1 <;> first | rfl | (dsimp only [a,b,result]; omega)

end ProductCallback
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
