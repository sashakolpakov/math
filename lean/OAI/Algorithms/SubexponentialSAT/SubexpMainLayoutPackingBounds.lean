import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutChoicesTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingBounds

namespace OAI.Algorithms

/-!
# Packing cost at the actual layout boundary

All packing source-size summands are read from selected physical words.
The universal-type count is obtained from the already-produced type stream
on master 10, whose preservation is proved from the actual tail trace.
No bound on the pending-leaf stream or on global machine storage is used.
-/

namespace SubexponentialSAT.SubexpMainLayoutPackingBounds

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master)
open SubexpMainLayoutWordBounds (RelevantWordBound)
open SubexpMainLayoutChoices (Result)
open SubexpMainLayoutChoicesTrace (TailTrace)

private theorem master_length_le {er es W : ℕ} {a : MainState er es}
    (h : RelevantWordBound W a) (alloc : Allocation es) (i : Fin 32) :
    (a.stacks (master alloc i)).length ≤ W := by
  apply h
  left
  have hi := i.isLt
  change 640 + i.val < 672
  omega

theorem storageSize_le {er es W : ℕ} (alloc : Allocation es) (a : MainState er es)
    (h : RelevantWordBound W a) : SubexpMainPacking.storageSize alloc a ≤ 61 * W := by
  change (∑ i : Fin 61, (a.stacks (SubexpMainPacking.stackMap alloc i)).length) ≤ 61 * W
  exact SubexpMainLayoutWordBounds.sum_lengths h (SubexpMainPacking.stackMap alloc)
    (fun i => Or.inl (SubexpMainPacking.stackMap_val_lt alloc i))

/-- The additional type word is an actual stored input from the earlier
universal-type stage, not an independently assumed cardinality bound. -/
theorem sourceSize_le {U : Type*} [DecidableEq U] {er es W : ℕ}
    (alloc : Allocation es) (a : MainState er es) (s : PackingExecution.Spec U)
    (h : RelevantWordBound W a) (hi : SubexpMainPacking.inputs alloc a = s.params.input)
    (htypes : a.stacks (master alloc 10) =
      ProgramEncoding.encodeRecords (s.types.values.map s.encodeType)) :
    PackingExecutionBounds.sourceSize s ≤ 8 * W + 1 := by
  have hd := congrArg PackingProgram.Input.dimension hi
  have hdelta := congrArg PackingProgram.Input.degree hi
  have hw := congrArg PackingProgram.Input.width hi
  have hscope := congrArg PackingProgram.Input.scopes hi
  have hrows := congrArg PackingProgram.Input.assignment hi
  have halphabet := congrArg PackingProgram.Input.alphabet hi
  change a.stacks (master alloc 8) = List.replicate s.params.D true at hd
  change a.stacks (master alloc 7) = List.replicate s.params.Δ true at hdelta
  change a.stacks (master alloc 4) = s.params.width at hw
  change a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes s.params.scopes at hscope
  change a.stacks (master alloc 2) = s.params.rows.flatten at hrows
  change a.stacks (master alloc 3) = ProgramEncoding.encodeRecords s.params.alphabet at halphabet
  have hD := master_length_le h alloc 8
  have hΔ := master_length_le h alloc 7
  have hW := master_length_le h alloc 4
  have hS := master_length_le h alloc 0
  have hR := master_length_le h alloc 2
  have hA := master_length_le h alloc 3
  have hU := master_length_le h alloc 10
  rw [hd, List.length_replicate] at hD
  rw [hdelta, List.length_replicate] at hΔ
  rw [hw] at hW
  rw [hscope] at hS
  rw [hrows] at hR
  rw [halphabet] at hA
  rw [htypes] at hU
  have hcount := PackingTupleBounds.records_count_le (s.types.values.map s.encodeType)
  simp only [List.length_map] at hcount
  have hscopeCount := Encoding.length_encodeList_lower SubexpIncidencePlanScan.scopeBytes s.params.scopes
  change s.params.scopes.length + 1 ≤ (SubexpPlanAlphabetBase.scopeBytes s.params.scopes).length
    at hscopeCount
  unfold PackingExecutionBounds.sourceSize
  omega

def packingCoefficient : ℕ := 30000 * (62 + 81000000 * 8^12)

/-- Fixed degree twelve, with every source-size term derived from actual
selected words, including the represented universal-type stream. -/
theorem runtimeBound_le {U : Type*} [DecidableEq U] {er es W : ℕ}
    (alloc : Allocation es) (a : MainState er es) (s : PackingExecution.Spec U)
    (h : RelevantWordBound W a) (hi : SubexpMainPacking.inputs alloc a = s.params.input)
    (htypes : a.stacks (master alloc 10) =
      ProgramEncoding.encodeRecords (s.types.values.map s.encodeType)) :
    SubexpMainPacking.runtimeBound alloc a s ≤ packingCoefficient * (W + 1)^12 := by
  have hs := storageSize_le alloc a h
  have hsource := sourceSize_le alloc a s h hi htypes
  have hbase : W ≤ (W + 1)^12 := (Nat.le_succ W).trans (Nat.le_self_pow (by decide) _)
  have hone : 1 ≤ (W + 1)^12 := Nat.one_le_pow _ _ (by omega)
  have hstorage : 61 * W + 1 ≤ 62 * (W + 1)^12 := by omega
  have hsource' : PackingExecutionBounds.sourceSize s ≤ 8 * (W + 1) := by omega
  calc
    SubexpMainPacking.runtimeBound alloc a s ≤ SubexpMainPacking.polynomialBound alloc a s :=
      SubexpMainPacking.runtimeBound_le_polynomial alloc a s
    _ ≤ 30000 * (61 * W + 81000000 * (8 * (W + 1))^12 + 1) := by
      unfold SubexpMainPacking.polynomialBound
      gcongr
    _ ≤ 30000 * (62 * (W + 1)^12 + 81000000 * (8^12 * (W + 1)^12)) := by
      rw [mul_pow]
      omega
    _ = packingCoefficient * (W + 1)^12 := by unfold packingCoefficient; ring

noncomputable def prePacking {er es : ℕ} (alloc : Allocation es)
    (coefficientState : MainState er es) (p : ℕ) [Fact p.Prime] : MainState er es :=
  SubexpMainScalarFrameWidth.installed alloc
    (SubexpMainScalarAlphabet.installed alloc coefficientState p)

section Trace

variable {er es p r Q Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {hregs : 16 ≤ er}
variable {a start coefficientState packingState out : MainState er es}
variable {hr : 0 < r} {hQ : 0 < Q} {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable {result : Result alloc a out p r Q Δ R D hr hQ scopes hd tables}

theorem prePacking_universal
    (h : TailTrace alloc hregs a start coefficientState packingState out result) :
    (prePacking alloc coefficientState p).stacks (master alloc 10) =
      ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ) := by
  obtain ⟨hc, _⟩ := h.coefficientResult
  have hw : (prePacking alloc coefficientState p).stacks (master alloc 10) =
      (SubexpMainScalarAlphabet.installed alloc coefficientState p).stacks (master alloc 10) := by
    apply SubexpMainScalarFrameWidth.installed_frame
    · intro he
      have hv := congrArg Fin.val he
      change 660 = 650 at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      change 319 = 650 at hv
      omega
  have hs : (SubexpMainScalarAlphabet.installed alloc coefficientState p).stacks (master alloc 10) =
      coefficientState.stacks (master alloc 10) := by
    apply SubexpMainScalarAlphabet.installed_frame
    · intro i he
      have hv := congrArg Fin.val he
      change 640 + (21 + i.val) = 650 at hv
      omega
    · intro i he
      have hv := congrArg Fin.val he
      change i.val = 650 at hv
      have hi := i.isLt
      omega
  have hp : coefficientState.stacks (master alloc 10) = start.stacks (master alloc 10) := by
    apply hc.frame
    · change 64 ≤ 650
      decide
    · intro he
      have hv := congrArg Fin.val he
      change 650 = 649 at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      change 650 = 254 at hv
      omega
  exact hw.trans (hs.trans (hp.trans h.startResult.universal))

theorem prePacking_types
    (h : TailTrace alloc hregs a start coefficientState packingState out result) :
    (prePacking alloc coefficientState p).stacks (master alloc 10) =
      ProgramEncoding.encodeRecords (result.packing.types.values.map result.packing.encodeType) := by
  change (prePacking alloc coefficientState p).stacks (master alloc 10) =
    ProgramEncoding.encodeRecords ((PackingCanonicalSpec.types hr hQ Δ).values.map
      CollisionProgram.encodeType)
  rw [PackingCanonicalSpec.types_bytes]
  exact prePacking_universal h

theorem packing_runtimeBound_le {W : ℕ}
    (h : TailTrace alloc hregs a start coefficientState packingState out result)
    (hw : RelevantWordBound W (prePacking alloc coefficientState p)) :
    SubexpMainPacking.runtimeBound alloc (prePacking alloc coefficientState p) result.packing ≤
      packingCoefficient * (W + 1)^12 :=
  runtimeBound_le alloc _ result.packing hw h.packingInputs (prePacking_types h)

theorem packing_run_bounded {W : ℕ}
    (h : TailTrace alloc hregs a start coefficientState packingState out result)
    (hw : RelevantWordBound W (prePacking alloc coefficientState p)) :
    SubexpMainLayoutChoicesTrace.Run (SubexpMainPacking.procedure er alloc)
      (packingCoefficient * (W + 1)^12) (prePacking alloc coefficientState p) packingState := by
  obtain ⟨steps, hs, he⟩ := h.packingRun
  exact ⟨steps, hs.trans (packing_runtimeBound_le h hw), he⟩

end Trace

end SubexponentialSAT.SubexpMainLayoutPackingBounds

end OAI.Algorithms
