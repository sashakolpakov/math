import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStoreTransitions

namespace OAI.Algorithms

/-!
# Basis readiness from the indexed node workspace

The master relation names only physically retained input words. The current
node index and every empty work cell follow from the published indexed-store
description. No scratch invariant or execution trace is an input field.
-/

namespace SubexponentialSAT.SubexpNodeBasisWorkspace

open BitProgram StructuredCalls
open SubexpNodeWorkspace (Store MasterPort initialStacks activeStacks)
open SubexpNodeStoreTransitions (cached indexed)
open Subexp.GlobalBasisInput (Context)

abbrev Data := SubexpNodeBasisStage.Data

/-- The ten retained copy sources, the local-batch position, and three
bank constants. The eleventh copy source116 is the physically written index. -/
structure Masters {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers rows : ℕ) (before : List (List Bool)) (tail : List Bool)
    (masters : Store) : Prop where
  width : masters 276 = List.replicate (Subexp.GlobalBasisEntry.frameWidth p) true
  zero : masters 282 = Subexp.GlobalBasisEntry.scalarFrame p 0
  one : masters 283 = Subexp.GlobalBasisEntry.scalarFrame p 1
  metadata : masters 269 = Subexp.SelectorProgram.rawRecords C.metadata
  universal : masters 266 = ProgramEncoding.encodeRecords
    (Subexp.TypeEnumeration.universalBytes r Q Δ)
  colors : masters 261 = List.replicate r true
  group : masters 270 = Subexp.GlobalBasisRecordLookup.recordsPrefix before ++
    Subexp.GlobalBasisRecordLookup.record C.batch ++ tail
  groupIndex : before.length = C.position.val
  dimension : masters 264 = List.replicate rows true
  blocks : masters 271 = List.replicate count true
  leftovers : masters 272 = List.replicate leftovers true
  modulus : masters 279 = Subexp.MatrixWordEncoding.modulus p
  zeroWord : masters 277 = Subexp.MatrixWordEncoding.zero p
  tokens : masters 280 =
    ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.tokens p)

theorem indexed_frame (masters : Store) (node cache index : List Bool)
    (i : Fin 288) (hi : 138 ≤ i.val) :
    indexed masters node cache index i = initialStacks masters i := by
  have hne (j : Fin 288) (hj : j.val < 138) : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    omega
  simp only [indexed, cached, activeStacks,
    Function.update_of_ne (hne 116 (by decide)),
    Function.update_of_ne (hne 102 (by decide)),
    Function.update_of_ne (hne 81 (by decide)),
    Function.update_of_ne (hne 74 (by decide)),
    Function.update_of_ne (hne 73 (by decide)),
    Function.update_of_ne (hne 66 (by decide)),
    Function.update_of_ne (hne 101 (by decide)),
    Function.update_of_ne (hne 100 (by decide)),
    Function.update_of_ne (hne 78 (by decide))]

theorem indexed_master (masters : Store) (node cache index : List Bool)
    (i : Fin 288) (hi : 255 ≤ i.val) :
    indexed masters node cache index i = masters i := by
  rw [indexed_frame masters node cache index i (by omega)]
  apply SubexpNodeWorkspace.initial_master
  unfold MasterPort
  omega

theorem indexed_work (masters : Store) (node cache index : List Bool)
    (i : Fin 288) (hlo : 138 ≤ i.val) (hhi : i.val < 255) :
    indexed masters node cache index i = [] := by
  rw [indexed_frame masters node cache index i hlo]
  apply SubexpNodeWorkspace.initial_empty
  simp only [MasterPort, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  omega

theorem indexed_temporary (masters : Store) (node cache index : List Bool) :
    indexed masters node cache index 0 = [] := rfl

theorem indexed_position (masters : Store) (node cache index : List Bool) :
    indexed masters node cache index 116 = index := by
  exact Function.update_self 116 index (cached masters node cache)

variable {p r Q Δ count leftovers rows : ℕ} [Fact p.Prime]
variable {C : Context p r Q Δ} {before : List (List Bool)} {tail : List Bool}
variable {masters : Store} {node cache : List Bool} {d : Data}

/-- The published indexed-store state implies all native input and scratch
requirements of the actual basis stage. Registers are unrestricted. -/
theorem input (H : Masters C count leftovers rows before tail masters)
    (hstate : d.stacks = indexed masters node cache (List.replicate C.position.val true)) :
    SubexpNodeBasisExecution.Input C count leftovers rows before tail d := by
  constructor
  · rw [hstate]
    exact indexed_temporary masters node cache _
  · rw [hstate, indexed_master masters node cache _ 276 (by decide)]
    exact H.width
  · rw [hstate, indexed_master masters node cache _ 282 (by decide)]
    exact H.zero
  · rw [hstate, indexed_master masters node cache _ 283 (by decide)]
    exact H.one
  · rw [hstate, indexed_position]
  · rw [hstate, indexed_master masters node cache _ 269 (by decide)]
    exact H.metadata
  · rw [hstate, indexed_master masters node cache _ 266 (by decide)]
    exact H.universal
  · rw [hstate, indexed_master masters node cache _ 261 (by decide)]
    exact H.colors
  · rw [hstate, indexed_master masters node cache _ 270 (by decide)]
    exact H.group
  · exact H.groupIndex
  · rw [hstate, indexed_master masters node cache _ 264 (by decide)]
    exact H.dimension
  · rw [hstate, indexed_master masters node cache _ 271 (by decide)]
    exact H.blocks
  · rw [hstate, indexed_master masters node cache _ 272 (by decide)]
    exact H.leftovers
  · intro i
    rw [hstate]
    apply indexed_work
    · change 138 ≤ 138 + i.val
      omega
    · change 138 + i.val < 255
      omega

/-- All additional bank scratch cells also come from the indexed state. -/
theorem bankStatics (H : Masters C count leftovers rows before tail masters)
    (hstate : d.stacks = indexed masters node cache (List.replicate C.position.val true)) :
    SubexpNodeBasisExecution.BankStatics p d := by
  constructor
  · rw [hstate, indexed_master masters node cache _ 279 (by decide)]
    exact H.modulus
  · rw [hstate, indexed_master masters node cache _ 277 (by decide)]
    exact H.zeroWord
  · rw [hstate, indexed_master masters node cache _ 280 (by decide)]
    exact H.tokens
  · intro i hlo hhi
    rw [hstate]
    exact indexed_work masters node cache _ i (by omega) (by omega)

theorem input_and_statics (H : Masters C count leftovers rows before tail masters)
    (hstate : d.stacks = indexed masters node cache (List.replicate C.position.val true)) :
    SubexpNodeBasisExecution.Input C count leftovers rows before tail d ∧
      SubexpNodeBasisExecution.BankStatics p d :=
  ⟨input H hstate, bankStatics H hstate⟩

end SubexponentialSAT.SubexpNodeBasisWorkspace

end OAI.Algorithms
