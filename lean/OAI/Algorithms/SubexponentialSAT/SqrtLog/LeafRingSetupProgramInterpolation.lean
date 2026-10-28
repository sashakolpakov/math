import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramLengths

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev Data := StructuredProgram.State 40 768

abbrev clear (dst : Fin 768) : Cmd 40 768 :=
  .call (clearProgram dst 38 39)

abbrev copy (src dst : Fin 768) : Cmd 40 768 :=
  .call (copyProgram src dst 699 38 39)

theorem clear_eval (dst : Fin 768) (a : Data) :
    Eval (clear dst) (2*(a.stacks dst).length+3) a
      ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst []⟩ :=
  Subexp.TupleProgram.clear_eval dst 38 39 a

theorem copy_eval (src dst : Fin 768) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 699) (hd : (699 : Fin 768) ≠ dst)
    (hw : a.stacks 699 = []) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a
      ⟨readRegs a.regs 38 39 none,
        Function.update a.stacks dst (a.stacks src ++ a.stacks dst)⟩ :=
  Subexp.TupleProgram.copy_eval src dst 699 38 39 hsd hs hd (by decide) a hw

abbrev overwrite (src dst : Fin 768) : Cmd 40 768 :=
  .seq (clear dst) (copy src dst)

/-- Clear the destination before copying.  This supports reuse of physical
scratch without requiring its previous value to vanish for free. -/
theorem overwrite_eval (src dst : Fin 768) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 699) (hd : (699 : Fin 768) ≠ dst)
    (hw : a.stacks 699 = []) :
    Eval (overwrite src dst) (2*(a.stacks dst).length+7*(a.stacks src).length+8) a
      ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst (a.stacks src)⟩ := by
  let b : Data := ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst []⟩
  have hc := clear_eval dst a
  have hp := copy_eval src dst b hsd hs hd (by simpa [b, hd] using hw)
  convert hc.seq hp using 1 <;>
    simp [ b, hsd, readRegs_reset] ; omega


def clearPorts : List (Fin 768) → Cmd 40 768
  | [] => .base .skip
  | p :: ps => .seq (clear p) (clearPorts ps)

def clearResult (a : Data) (p : Fin 768) : Data :=
  ⟨readRegs a.regs 38 39 none, Function.update a.stacks p []⟩

def clearedPorts : List (Fin 768) → Data → Data
  | [], a => a
  | p :: ps, a => clearedPorts ps (clearResult a p)

def clearPortsCost : List (Fin 768) → Data → ℕ
  | [], _ => 0
  | p :: ps, a => 2*(a.stacks p).length+3+clearPortsCost ps (clearResult a p)

theorem clearPorts_eval (ps : List (Fin 768)) (a : Data) :
    Eval (clearPorts ps) (clearPortsCost ps a) a (clearedPorts ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih => exact (clear_eval p a).seq (ih _)

theorem clearedPorts_stacks (ps : List (Fin 768)) (a : Data) (i : Fin 768) :
    (clearedPorts ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearedPorts]
  | cons p ps ih =>
    simp only [clearedPorts, ih, List.mem_cons, clearResult]
    by_cases hi : i=p
    · subst i
      simp
    · by_cases hm : i ∈ ps <;> simp [hi,hm]

theorem clearPortsCost_bound (ps : List (Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀ p ∈ ps, (a.stacks p).length ≤ W) :
    clearPortsCost ps a ≤ ps.length*(2*W+3) := by
  induction ps generalizing a with
  | nil => simp [clearPortsCost]
  | cons p ps ih =>
    have hp := hw p (by simp)
    have htail : ∀ q ∈ ps, ((clearResult a p).stacks q).length ≤ W := by
      intro q hq
      by_cases h : q=p
      · simp [clearResult,h]
      · simpa [clearResult,h] using hw q (by simp [hq])
    have ht := ih (clearResult a p) htail
    simp only [clearPortsCost, List.length_cons]
    nlinarith


def copyPlan : List (Fin 768 × Fin 768) → Cmd 40 768
  | [] => .base .skip
  | p::ps => .seq (overwrite p.1 p.2) (copyPlan ps)

def copied (p : Fin 768 × Fin 768) (a : Data) : Data :=
  ⟨readRegs a.regs 38 39 none,Function.update a.stacks p.2 (a.stacks p.1)⟩

def copiedPlan : List (Fin 768 × Fin 768) → Data → Data
  | [],a => a
  | p::ps,a => copiedPlan ps (copied p a)

def copyPlanCost : List (Fin 768 × Fin 768) → Data → ℕ
  | [],_ => 0
  | p::ps,a => 2*(a.stacks p.2).length+7*(a.stacks p.1).length+8+
      copyPlanCost ps (copied p a)

theorem copyPlan_eval (ps : List (Fin 768 × Fin 768)) (a : Data)
    (hports : ∀ p∈ps,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699)
    (hwork : a.stacks 699=[]) :
    Eval (copyPlan ps) (copyPlanCost ps a) a (copiedPlan ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih =>
    have hp := hports p (by simp)
    have he := overwrite_eval p.1 p.2 a hp.1 hp.2.1 (Ne.symm hp.2.2) hwork
    have ht := ih (copied p a) (fun q hq => hports q (by simp [hq]))
      (by simpa [copied,hp.2.2,Ne.symm hp.2.2] using hwork)
    exact he.seq ht

theorem copyPlanCost_bound (ps : List (Fin 768 × Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) :
    copyPlanCost ps a ≤ ps.length*(9*W+8) := by
  induction ps generalizing a with
  | nil => simp [copyPlanCost]
  | cons p ps ih =>
    have hb : ∀ i,((copied p a).stacks i).length ≤ W := by
      intro i
      by_cases hi : i=p.2
      · simpa [copied,hi] using hw p.1
      · simpa [copied,hi] using hw i
    have ht := ih (copied p a) hb
    have hs := hw p.1
    have hd := hw p.2
    simp only [copyPlanCost,List.length_cons]
    nlinarith

theorem copiedPlan_frame (ps : List (Fin 768 × Fin 768)) (a : Data) (i : Fin 768)
    (hi : ∀ p∈ps,i≠p.2) : (copiedPlan ps a).stacks i=a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copiedPlan,ih (copied p a) (fun q hq => hi q (by simp [hq]))]
    simp [copied,hi p (by simp)]



def localRegisters (i : Fin 16) : Fin 40 := i.castLE (by decide)
def localPorts (i : Fin 320) : Fin 768 := ⟨340+i.val,by omega⟩
theorem localRegisters_injective : Function.Injective localRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 40 => x.val) h
theorem localPorts_injective : Function.Injective localPorts := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [localPorts] at this; omega

def privatePorts : List (Fin 768) := (List.finRange 320).map localPorts

theorem privatePorts_mem (i : Fin 320) : localPorts i ∈ privatePorts := by
  exact List.mem_map_of_mem (List.mem_finRange i)

theorem privatePorts_not_low (i : Fin 768) (hi : i.val < 340) : i∉privatePorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hh := congrArg Fin.val hj
  dsimp [localPorts] at hh
  omega

theorem privatePorts_not_high (i : Fin 768) (hi : 660 ≤ i.val) : i∉privatePorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hh := congrArg Fin.val hj
  dsimp [localPorts] at hh
  omega

def inputPlan : List (Fin 768 × Fin 768) :=
  [(280,444),(194,534),(201,541),(202,542),(203,543),(204,544),
   (207,547),(209,549),(211,551),(212,552),(256,596)]

def outputPlan : List (Fin 768 × Fin 768) :=
  [(599,713),(600,714),(601,715),(602,716),(603,717)]

theorem inputPlan_ports : ∀p∈inputPlan,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699 := by
  intro p hp
  simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem outputPlan_ports : ∀p∈outputPlan,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699 := by
  intro p hp
  simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide

abbrev coreCall : Cmd 40 768 := .call
  (ProgramLinking.liftProgram InterpolationCacheProgram.program localRegisters localPorts)

abbrev command : Cmd 40 768 :=
  .seq (clearPorts (699::privatePorts)) (.seq (copyPlan inputPlan)
    (.seq coreCall (.seq (copyPlan outputPlan) (clearPorts privatePorts))))

def program := compiled command 256 715

/-- The central call is exactly the verified finite cache producer, with no
replacement of its inverse or difference tables by semantic values. -/
theorem coreCall_eval (base : Data) (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne : InterpolationCacheProgram.Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : InterpolationCacheProgram.Store)
    (xs : List (InterpolationCacheProgram.Coeff t d))
    (hr : InterpolationCacheProgram.Ready t a M cache minusOne s)
    (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈InterpolationCacheProgram.inputEmpty,s i=[])
    (hs : ∀i,base.stacks (localPorts i)=s i) :
    ∃n ≤ InterpolationCacheProgram.budget t d xs.length+1,∃rf,
      Eval coreCall n base (embedState localRegisters localPorts base
        (⟨rf,InterpolationCacheProgram.finalStore t a M cache minusOne xs s⟩ :
          InterpolationCacheProgram.Data)) := by
  obtain ⟨n,rf,hn,he⟩ := InterpolationCacheProgram.program_run t a M cache hz minusOne hW
    s xs hr hm hc (base.regs ∘ localRegisters)
  have hp : projectState localRegisters localPorts base=
      (⟨base.regs ∘ localRegisters,s⟩ : InterpolationCacheProgram.Data) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; exact hs i
  exact ⟨n,hn,rf,eval_call_from_state InterpolationCacheProgram.program
    localRegisters localPorts base localRegisters_injective localPorts_injective (hp.symm ▸ he)⟩

/-- Caller preparation is a concrete clear/copy program. Its logical store
is named only to state the interface to the native cache producer. -/
def staged (base : Data) : Data :=
  copiedPlan inputPlan (clearedPorts (699::privatePorts) base)

def stagedStore (base : Data) : InterpolationCacheProgram.Store :=
  fun i => (staged base).stacks (localPorts i)

def stagedCost (base : Data) : ℕ :=
  clearPortsCost (699::privatePorts) base+
    copyPlanCost inputPlan (clearedPorts (699::privatePorts) base)

theorem stage_eval (base : Data) :
    Eval (.seq (clearPorts (699::privatePorts)) (copyPlan inputPlan))
      (stagedCost base) base (staged base) := by
  have h0 := clearPorts_eval (699::privatePorts) base
  have h1 := copyPlan_eval inputPlan (clearedPorts (699::privatePorts) base)
    inputPlan_ports (by simp [clearedPorts_stacks])
  exact h0.seq h1

def inputIndex : Fin 320 → Option (Fin 768) := fun i =>
  if i=104 then some 280 else if i=194 then some 194 else
  if i=201 then some 201 else if i=202 then some 202 else
  if i=203 then some 203 else if i=204 then some 204 else
  if i=207 then some 207 else if i=209 then some 209 else
  if i=211 then some 211 else if i=212 then some 212 else
  if i=256 then some 256 else none

/-- Exact input-byte certificate for the paid staging operation. -/
theorem stagedStore_eq (base : Data) (i : Fin 320) :
    stagedStore base i=((inputIndex i).map base.stacks).getD [] := by
  have hz : (clearedPorts (699::privatePorts) base).stacks (localPorts i)=[] := by
    simp only [clearedPorts_stacks]
    simp [privatePorts_mem i]
  have hl (j : Fin 768) (hj : j.val < 340) :
      (clearedPorts (699::privatePorts) base).stacks j=base.stacks j := by
    have hn := privatePorts_not_low j hj
    have h699 : j≠699 := by
      intro he
      subst j
      change (699 : ℕ) < 340 at hj
      omega
    simp [clearedPorts_stacks,hn,h699]
  have h280 := hl 280 (by decide)
  have h194 := hl 194 (by decide)
  have h201 := hl 201 (by decide)
  have h202 := hl 202 (by decide)
  have h203 := hl 203 (by decide)
  have h204 := hl 204 (by decide)
  have h207 := hl 207 (by decide)
  have h209 := hl 209 (by decide)
  have h211 := hl 211 (by decide)
  have h212 := hl 212 (by decide)
  have h256 := hl 256 (by decide)
  by_cases h104 : i = 104
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h194i : i = 194
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h201i : i = 201
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h202i : i = 202
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h203i : i = 203
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h204i : i = 204
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h207i : i = 207
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h209i : i = 209
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h211i : i = 211
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h212i : i = 212
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h256i : i = 256
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  have hv104 : i.val ≠ 104 := fun h => h104 (Fin.ext h)
  have hv194 : i.val ≠ 194 := fun h => h194i (Fin.ext h)
  have hv201 : i.val ≠ 201 := fun h => h201i (Fin.ext h)
  have hv202 : i.val ≠ 202 := fun h => h202i (Fin.ext h)
  have hv203 : i.val ≠ 203 := fun h => h203i (Fin.ext h)
  have hv204 : i.val ≠ 204 := fun h => h204i (Fin.ext h)
  have hv207 : i.val ≠ 207 := fun h => h207i (Fin.ext h)
  have hv209 : i.val ≠ 209 := fun h => h209i (Fin.ext h)
  have hv211 : i.val ≠ 211 := fun h => h211i (Fin.ext h)
  have hv212 : i.val ≠ 212 := fun h => h212i (Fin.ext h)
  have hv256 : i.val ≠ 256 := fun h => h256i (Fin.ext h)
  change (copiedPlan inputPlan (clearedPorts (699::privatePorts) base)).stacks
      (localPorts i) = ((inputIndex i).map base.stacks).getD []
  rw [copiedPlan_frame inputPlan]
  · simpa [stagedStore,staged,inputIndex,h104,h194i,h201i,h202i,h203i,h204i,
      h207i,h209i,h211i,h212i,h256i] using hz
  · intro p hp
    simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      intro he <;> have hh := congrArg Fin.val he <;> dsimp [localPorts] at hh <;> omega

/-- All native workspace assumptions follow from literal empty staged
bytes. This fact makes no assumption about the caller's previous scratch. -/
theorem staged_inputEmpty (base : Data) :
    ∀i∈InterpolationCacheProgram.inputEmpty,stagedStore base i=[] := by
  intro i hi
  rw [stagedStore_eq]
  simp only [InterpolationCacheProgram.inputEmpty,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- These are the retained physical bytes of ring setup, not an additional
arithmetic-service oracle. Every private workspace byte is supplied by the
paid clearing operation above. -/
structure Inputs (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : InterpolationCacheProgram.Coeff t d) (base : Data) : Prop where
  modulus : base.stacks 194=M.bits
  table : base.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t model M cache)
  width : (base.stacks 202).length=baseWidth 3 t
  scalarZero : base.stacks 203=cache.zero.val
  degree : (base.stacks 204).length=d
  zero : base.stacks 280=RingProgram.flat (RingProgram.modelProgram t model M cache).zeroRun.1
  one : base.stacks 207=RingProgram.flat (RingProgram.modelProgram t model M cache).oneRun.1
  minus : base.stacks 211=RingProgram.flat minusOne
  exponent : (base.stacks 209).length=3^d-2
  precision : (base.stacks 212).length=t

theorem staged_ready (base : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : InterpolationCacheProgram.Coeff t d)
    (h : Inputs t model M cache minusOne base) :
    InterpolationCacheProgram.Ready t model M cache minusOne (stagedStore base) := by
  constructor
  · constructor
    · constructor
      · simp [InterpolationCacheProgram.low,stagedStore_eq,inputIndex]
      · intro i
        fin_cases i <;>
          simp [ReconstructionProgram.RingAdapter.ports,ReconstructionProgram.RingAdapter.finalNative,ReconstructionProgram.RingAdapter.nativeStacks,
            InterpolationCacheProgram.low,stagedStore_eq,inputIndex,h.modulus,h.table,
            h.scalarZero]
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.modulus
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.width
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.scalarZero
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.table
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.degree
  · simpa [stagedStore_eq,inputIndex] using h.zero
  · simpa [stagedStore_eq,inputIndex] using h.one
  · simpa [stagedStore_eq,inputIndex] using h.minus
  · simpa [stagedStore_eq,inputIndex] using h.exponent
  · simpa [stagedStore_eq,inputIndex] using h.precision
  · intro i hi
    rw [stagedStore_eq]
    simp only [InterpolationCacheProgram.scratchPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The actual ring producer discharges the staged byte interface. The
remaining equality is the numerical bank's field-cardinality identity. -/
theorem inputs_of_produced (base : Data) (a : LeafRingSetupProgram.Data)
    (m : LeafParametersProgram.Circuit.Model) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33))
    (hp : Produced m hd M cache u a)
    (hb : ∀i,base.stacks (wideStacks i)=a.stacks i)
    (hexp : (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code m).val 44=
      3^(m.val 34)-2) :
    Inputs (m.val 33) (IrreducibleSearch.data hd) M cache
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) base := by
  constructor
  · exact (hb 194).trans hp.caches.modulus
  · exact (hb 201).trans hp.native.table
  · rw [show base.stacks 202=a.stacks 202 from hb 202]; exact hp.caches.width
  · exact (hb 203).trans hp.caches.scalarZero
  · rw [show base.stacks 204=a.stacks 204 from hb 204]; exact hp.caches.degree
  · exact (hb 280).trans hp.caches.fullZero_model
  · exact (hb 207).trans hp.caches.fullOne_model
  · exact (hb 211).trans (hp.caches.fullMinusOne.trans
      (LeafProgram.Constants.constantCode_flat _ _ _).symm)
  · rw [show base.stacks 209=a.stacks 209 from hb 209,hp.exponent,List.length_replicate]
    exact hexp
  · rw [show base.stacks 212=a.stacks 212 from hb 212,hp.caches.precision,List.length_replicate]

theorem cleared_width (ps : List (Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,((clearedPorts ps a).stacks i).length ≤ W := by
  intro i; rw [clearedPorts_stacks]; split_ifs <;> simp_all

theorem copied_width (ps : List (Fin 768 × Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,((copiedPlan ps a).stacks i).length ≤ W := by
  induction ps generalizing a with
  | nil => exact hw
  | cons p ps ih =>
    apply ih
    intro i
    by_cases hi : i=p.2
    · simpa [copied,hi] using hw p.1
    · simpa [copied,hi] using hw i

theorem eval_width {c : Cmd 40 768} {n W : ℕ} {a e : Data}
    (he : Eval c n a e) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,(e.stacks i).length ≤ W+n+1 := by
  intro i
  have h := Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace he 0 0) i
  simp only [] at h
  have := hw i
  omega

theorem cleared_register_frame (ps : List (Fin 768)) (a : Data)
    (i : Fin 40) (h38 : i≠38) (h39 : i≠39) :
    (clearedPorts ps a).regs i=a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [clearedPorts,ih]
    simp [clearResult,readRegs,h38,h39]

theorem copied_register_frame (ps : List (Fin 768 × Fin 768)) (a : Data)
    (i : Fin 40) (h38 : i≠38) (h39 : i≠39) :
    (copiedPlan ps a).regs i=a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copiedPlan,ih]
    simp [copied,readRegs,h38,h39]

/-- All five cache outputs, including unary lengths, are generated and
extracted by the fixed program. Old scratch need not initially be empty. -/
theorem command_eval (base : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne : InterpolationCacheProgram.Coeff t d) (hW : 0 < d*baseWidth 3 t)
    (xs : List (InterpolationCacheProgram.Coeff t d))
    (hi : Inputs t model M cache minusOne base)
    (hm : base.stacks 256=xs.flatMap RingProgram.flat)
    (W : ℕ) (hw : ∀i,(base.stacks i).length ≤ W) :
    ∃n ≤ 10000*(W+InterpolationCacheProgram.budget t d xs.length+2),∃e : Data,
      Eval command n base e ∧
      e.stacks 713=InterpolationCacheProgram.inverseBytes t model M cache minusOne xs ∧
      e.stacks 714=InterpolationCacheProgram.negativeBytes t model M cache minusOne xs ∧
      e.stacks 715=InterpolationCacheProgram.differenceBytes t model M cache minusOne xs ∧
      e.stacks 716=List.replicate (xs.length*(d*baseWidth 3 t)) true ∧
      e.stacks 717=List.replicate (d*baseWidth 3 t) true ∧
      (∀i∈privatePorts,e.stacks i=[]) ∧
      (∀i,i∉privatePorts → i≠699 → i∉([713,714,715,716,717] : List (Fin 768)) →
        e.stacks i=base.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → i.val < 38 → e.regs i=base.regs i) := by
  let a0 := clearedPorts (699::privatePorts) base
  let a1 := staged base
  have he0 := clearPorts_eval (699::privatePorts) base
  have he1 := copyPlan_eval inputPlan a0 inputPlan_ports
    (by simp [a0,clearedPorts_stacks])
  have hw0 := cleared_width (699::privatePorts) base W hw
  have hw1 := copied_width inputPlan a0 W hw0
  have hs1 : a1.stacks 699=[] := by
    simp [a1,staged,inputPlan,copiedPlan,copied,clearedPorts_stacks]
  have hm1 : stagedStore base 256=xs.flatMap RingProgram.flat := by
    simpa [stagedStore_eq,inputIndex] using hm
  obtain ⟨nc,hnc,rf,hec⟩ := coreCall_eval a1 t model M cache hz minusOne hW
    (stagedStore base) xs (staged_ready base t model M cache minusOne hi) hm1
    (staged_inputEmpty base) (fun _=>rfl)
  let raw : InterpolationCacheProgram.Data :=
    ⟨rf,InterpolationCacheProgram.finalStore t model M cache minusOne xs (stagedStore base)⟩
  let a2 := embedState localRegisters localPorts a1 raw
  have hs2 : a2.stacks 699=[] := by
    rw [show a2.stacks 699=a1.stacks 699 from
      embedState_stack_frame _ _ _ _ _ (by
        rintro ⟨i,h⟩; have := congrArg Fin.val h; dsimp [localPorts] at this; omega)]
    exact hs1
  have hp := copyPlan_eval outputPlan a2 outputPlan_ports hs2
  let a3 := copiedPlan outputPlan a2
  let e := clearedPorts privatePorts a3
  have he3 := clearPorts_eval privatePorts a3
  have hwidth := eval_width hec hw1
  have hw2 : ∀i,(a2.stacks i).length ≤ W+InterpolationCacheProgram.budget t d xs.length+2 := by
    intro i
    have hh := hwidth i
    change (a2.stacks i).length ≤ W+nc+1 at hh
    omega
  have hw3 := copied_width outputPlan a2 _ hw2
  have hb0 := clearPortsCost_bound (699::privatePorts) base W (fun i _=>hw i)
  have hb1 := copyPlanCost_bound inputPlan a0 W hw0
  have hbo := copyPlanCost_bound outputPlan a2 _ hw2
  have hb3 := clearPortsCost_bound privatePorts a3 _ (fun i _=>hw3 i)
  have hout (i : Fin 320) : a2.stacks (localPorts i)=raw.stacks i :=
    embedState_stack _ _ _ _ localPorts_injective i
  have h599 : a2.stacks 599=InterpolationCacheProgram.inverseBytes t model M cache minusOne xs := hout 259
  have h600 : a2.stacks 600=InterpolationCacheProgram.negativeBytes t model M cache minusOne xs := hout 260
  have h601 : a2.stacks 601=InterpolationCacheProgram.differenceBytes t model M cache minusOne xs := hout 261
  have h602 : a2.stacks 602=List.replicate (xs.length*(d*baseWidth 3 t)) true := hout 262
  have h603 : a2.stacks 603=List.replicate (d*baseWidth 3 t) true := hout 263
  refine ⟨clearPortsCost (699::privatePorts) base+copyPlanCost inputPlan a0+
    nc+copyPlanCost outputPlan a2+clearPortsCost privatePorts a3,?_,e,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hprivate : privatePorts.length = 320 := by simp [privatePorts]
    simp only [List.length_cons,hprivate] at hb0 hb3
    norm_num [inputPlan] at hb1
    norm_num [outputPlan] at hbo
    unfold inputPlan outputPlan
    omega
  · simpa only [command,Nat.add_assoc,staged,a0,a1,a3,e] using
      he0.seq (he1.seq (hec.seq (hp.seq he3)))
  · simp [e,clearedPorts_stacks,privatePorts_not_high 713 (by decide),
      a3,copiedPlan,copied,outputPlan,h599]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 714 (by decide),
      a3,copiedPlan,copied,outputPlan,h600]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 715 (by decide),
      a3,copiedPlan,copied,outputPlan,h601]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 716 (by decide),
      a3,copiedPlan,copied,outputPlan,h602]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 717 (by decide),
      a3,copiedPlan,copied,outputPlan,h603]
  · intro i hi'; simp [e,clearedPorts_stacks,hi']
  · intro i hpriv h699 ho
    have hlocal : ¬∃j,localPorts j=i := by
      rintro ⟨j,rfl⟩; exact hpriv (by simp [privatePorts])
    have hdout : ∀p∈outputPlan,p.2≠i := by
      intro p hp'
      simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp'
      rcases hp' with rfl|rfl|rfl|rfl|rfl <;> intro hh <;> subst i <;> simp at ho
    have hdin : ∀p∈inputPlan,p.2≠i := by
      intro p hp' hh
      have hpv : p.2∈privatePorts := by
        simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp'
        rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      exact hpriv (hh ▸ hpv)
    rw [show e.stacks i=a3.stacks i by simp [e,clearedPorts_stacks,hpriv]]
    rw [show a3.stacks i=a2.stacks i from copiedPlan_frame outputPlan a2 i (fun p hp => Ne.symm (hdout p hp))]
    rw [show a2.stacks i=a1.stacks i from embedState_stack_frame _ _ _ _ _ hlocal]
    rw [show a1.stacks i=a0.stacks i from copiedPlan_frame inputPlan a0 i (fun p hp => Ne.symm (hdin p hp))]
    simp [a0,clearedPorts_stacks,hpriv,h699]
  · intro i hlo hhi
    have h38 : i≠38 := by intro he; subst i; omega
    have h39 : i≠39 := by intro he; subst i; omega
    rw [show e.regs i=a3.regs i from cleared_register_frame privatePorts a3 i h38 h39]
    rw [show a3.regs i=a2.regs i from copied_register_frame outputPlan a2 i h38 h39]
    rw [show a2.regs i=a1.regs i from embedState_register_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; have := congrArg Fin.val hj; dsimp [localRegisters] at this; omega)]
    rw [show a1.regs i=a0.regs i from copied_register_frame inputPlan a0 i h38 h39]
    exact cleared_register_frame (699::privatePorts) base i h38 h39

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
