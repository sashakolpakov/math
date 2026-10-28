import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisCopies
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMatrixBytes
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisNativeBounds

namespace OAI.Algorithms

/-!
# Actual basis production in the node worker

The input relation names the eleven stored words copied by the fixed stage.
The native basis execution is derived from the local-search and packing data.
The stage restores its private bank and changes only the matrix bundle on201.
-/

namespace SubexponentialSAT.SubexpNodeBasisExecution

open BitProgram StructuredCalls
open SubexpNodeBasisStage
open Subexp.GlobalBasisInput (Context Location)
open MulticolorTypes (UniversalType)
open Subexp.ConstructivePacking (PackingData)
open Subexp.BlockSearch (GoodPair)
open Subexp.GlobalBasisRefinement (packingLocation pairs)


/-- Stored source words and a clean private basis bank. No native execution
or global matrix is supplied by this relation. -/
structure Input {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers rows : ℕ) (before : List (List Bool)) (tail : List Bool)
    (d : Data) : Prop where
  temporary : d.stacks 0 = []
  width : d.stacks 276 = List.replicate (Subexp.GlobalBasisEntry.frameWidth p) true
  zero : d.stacks 282 = Subexp.GlobalBasisEntry.scalarFrame p 0
  one : d.stacks 283 = Subexp.GlobalBasisEntry.scalarFrame p 1
  position : d.stacks 116 = List.replicate C.position.val true
  metadata : d.stacks 269 = Subexp.SelectorProgram.rawRecords C.metadata
  universal : d.stacks 266 = ProgramEncoding.encodeRecords
    (Subexp.TypeEnumeration.universalBytes r Q Δ)
  colors : d.stacks 261 = List.replicate r true
  group : d.stacks 270 = Subexp.GlobalBasisRecordLookup.recordsPrefix before ++
    Subexp.GlobalBasisRecordLookup.record C.batch ++ tail
  groupIndex : before.length = C.position.val
  dimension : d.stacks 264 = List.replicate rows true
  blocks : d.stacks 271 = List.replicate count true
  leftovers : d.stacks 272 = List.replicate leftovers true
  work : WorkEmpty d

def nativeInput (d : Data) : Subexp.GlobalBasisProgram.Data := projectState id ports (copied moves d)

theorem native_read {d : Data} (h : WorkEmpty d) (src : Fin 288) (i : Fin 64)
    (hm : (src, ports i) ∈ moves) :
    (nativeInput d).stacks i = d.stacks src := copied_source h (src, ports i) hm

theorem native_empty {d : Data} (h : WorkEmpty d) (i : Fin 64)
    (hi : i ∉ suppliedPorts) : (nativeInput d).stacks i = [] :=
  (copied_native_frame d i hi).trans (h i)

/-- The eleven physical copies establish every native input field. -/
theorem native_inputs {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C count leftovers locs.length before tail d) :
    Subexp.GlobalBasisProgram.Inputs C count leftovers locs before tail (nativeInput d) := by
  constructor
  · exact (native_read H.work 276 13 (by decide)).trans H.width
  · exact (native_read H.work 282 14 (by decide)).trans H.zero
  · exact (native_read H.work 283 15 (by decide)).trans H.one
  · exact (native_read H.work 116 32 (by decide)).trans H.position
  · exact (native_read H.work 269 33 (by decide)).trans H.metadata
  · exact (native_read H.work 266 37 (by decide)).trans H.universal
  · exact (native_read H.work 261 38 (by decide)).trans H.colors
  · exact (native_read H.work 270 47 (by decide)).trans H.group
  · exact H.groupIndex
  · exact (native_read H.work 264 46 (by decide)).trans H.dimension
  · exact (native_read H.work 271 48 (by decide)).trans H.blocks
  · exact (native_read H.work 272 49 (by decide)).trans H.leftovers
  · intro i hi
    apply native_empty H.work i
    intro hm
    exact hi ((show suppliedPorts ⊆ Subexp.GlobalBasisProgram.retainedPorts from by decide) hm)
  · exact native_empty H.work 40 (by decide)
  · exact native_empty H.work 55 (by decide)
  · exact native_empty H.work 63 (by decide)

/-- Copying costs seven instructions per bit plus five per word; cleanup
costs two instructions per bit plus three per word. The remaining two are the native
return and the enclosing stage's halt. -/
def runtimeBound {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) (d : Data) : ℕ :=
  Subexp.GlobalBasisProgram.totalBudget C count leftovers locs (d.stacks 270).length +
    9 * inputVolume d + 90

theorem native_volume_le {d : Data} (h : WorkEmpty d) :
    Subexp.GlobalBasisNativeBounds.inputVolume (nativeInput d) ≤ inputVolume d + 1 := by
  unfold Subexp.GlobalBasisNativeBounds.inputVolume
  rw [native_read h 270 47 (by decide), native_read h 269 33 (by decide),
    native_read h 266 37 (by decide), native_read h 261 38 (by decide),
    native_read h 116 32 (by decide), native_read h 264 46 (by decide),
    native_read h 271 48 (by decide), native_read h 272 49 (by decide),
    native_read h 276 13 (by decide)]
  simp only [inputVolume, moves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- A uniform polynomial in the lengths of the actual eleven input words. -/
def inputBudget (d : Data) : ℕ :=
  1000000000000000099 * (inputVolume d + 2)^20

theorem runtimeBound_le_inputBudget {p r Q Δ : ℕ} [Fact p.Prime]
    (C : Context p r Q Δ) (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C count leftovers locs.length before tail d)
    (hm : C.locations 0 locs) :
    runtimeBound C count leftovers locs d ≤ inputBudget d := by
  have hn := native_inputs C count leftovers locs before tail d H
  have hb := Subexp.GlobalBasisNativeBounds.totalBudget_input_le hn hm
  rw [native_read H.work 270 47 (by decide)] at hb
  have hv := native_volume_le H.work
  have hp := Nat.pow_le_pow_left (by omega :
    Subexp.GlobalBasisNativeBounds.inputVolume (nativeInput d) + 1 ≤ inputVolume d + 2) 20
  have hb' := hb.trans (Nat.mul_le_mul_left 1000000000000000000 hp)
  have hlinear : inputVolume d + 2 ≤ (inputVolume d + 2)^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by omega : 1 ≤ inputVolume d + 2) (show 1 ≤ 20 by decide)
  unfold runtimeBound inputBudget
  omega

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))

/-- Actual node-worker execution, with exact global matrix bytes and an
output-only stack update. Local checker success and packing metadata are
used to derive the native basis theorem internally. -/
theorem program_runs_images
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C P.blockCount P.leftovers.length D before tail d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType) :
    ∃ e : Data,
      RunsIn program
        (runtimeBound C P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 201
        (ProgramEncoding.encodeRecords
          ((Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P).map
            SubexpNodeBankMap.payload)) := by
  have hn := native_inputs C P.blockCount P.leftovers.length
    (List.ofFn (packingLocation P)) before tail d
    (by simpa only [List.length_ofFn] using H)
  obtain ⟨out, ⟨n, hnBound, hnTrace⟩, hs⟩ := Subexp.GlobalBasisMatrixBytes.program_runsIn_images
    C hr hQ hsplit constraint good alphabet complete P before tail (nativeInput d) hn hmeta
  let e := embedState id ports (copied moves d) out
  have he := embedded_stacks (d := d) _ hs
  have hcost := cleanupCost_eq H.work _ he
  have htrace := program_trace_from_native d H.temporary n out hnTrace
  have hsource := native_read H.work 270 47 (by decide)
  have hresult := cleaned_stacks H.work _ he
  refine ⟨cleared workspace e, ⟨_, ?_, htrace⟩, hresult⟩
  rw [copyCost_eq, hcost]
  rw [hsource] at hnBound
  unfold runtimeBound
  omega

theorem program_runs_images_frame
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C P.blockCount P.leftovers.length D before tail d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType) :
    ∃ e : Data,
      RunsIn program
        (runtimeBound C P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 201 = ProgramEncoding.encodeRecords
        ((Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P).map
          SubexpNodeBankMap.payload) ∧
      (∀ i, i ≠ 201 → e.stacks i = d.stacks i) := by
  obtain ⟨e, he, hs⟩ := program_runs_images C hr hQ hsplit constraint good alphabet complete P
    before tail d H hmeta
  refine ⟨e, he, ?_, ?_⟩
  · simp only [hs, Function.update_self]
  · intro i hi
    simp only [hs, Function.update_of_ne hi]

/-- The same complete execution with a polynomial budget on physical input
lengths, using the native producer's checked size analysis. -/
theorem program_runs_images_bounded
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C P.blockCount P.leftovers.length D before tail d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType) :
    ∃ e : Data,
      RunsIn program (inputBudget d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 201 (ProgramEncoding.encodeRecords
        ((Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P).map
          SubexpNodeBankMap.payload)) := by
  obtain ⟨e, he, hs⟩ := program_runs_images C hr hQ hsplit constraint good alphabet complete P
    before tail d H hmeta
  refine ⟨e, he.mono ?_, hs⟩
  apply runtimeBound_le_inputBudget C P.blockCount P.leftovers.length
    (List.ofFn (packingLocation P)) before tail d
  · simpa only [List.length_ofFn] using H
  · exact Subexp.GlobalBasisRefinement.packing_locations C P hmeta

end SubexponentialSAT.SubexpNodeBasisExecution

end OAI.Algorithms
