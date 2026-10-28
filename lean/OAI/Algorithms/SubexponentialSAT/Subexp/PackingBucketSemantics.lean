import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketExecution

namespace OAI.Algorithms

/-! The physical bucket/minimum output is the existing computable packing. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open ConstructivePacking MatrixProgramSupport

variable {V U : Type*} [DecidableEq U]

theorem minimum_typed_aux (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (us : List U) (m : ℕ)
    (hm : m ≤ P.vertices.values.length) :
    minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (us.map encodeType) m = min m (P.minCount us) := by
  induction us generalizing m with
  | nil => simp [minimum, PackingData.minCount, Nat.min_eq_left hm]
  | cons u us ih =>
    simp only [minimum, List.map_cons, List.foldl_cons]
    rw [BucketProgram.constructive_bucket_output P encodeType encodeVertex hinj,
      List.length_map]
    change minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (us.map encodeType) (min m (P.bucket u).length) = _
    rw [ih _ ((min_le_left _ _).trans hm)]
    simp only [PackingData.minCount, Nat.min_assoc]

theorem minCount_le_vertices (P : PackingData V U) (us : List U) :
    P.minCount us ≤ P.vertices.values.length := by
  induction us with
  | nil => exact le_rfl
  | cons u us ih => exact (min_le_right _ _).trans ih

theorem minimum_eq_blockCount (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) :
    minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (P.types.values.map encodeType) P.vertices.values.length = P.blockCount := by
  rw [minimum_typed_aux P encodeType encodeVertex hinj _ _ le_rfl]
  exact Nat.min_eq_right (minCount_le_vertices P P.types.values)

theorem table_eq_typed (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) :
    table (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (P.types.values.map encodeType) =
      P.types.values.map (fun u => Encoding.frame (encodeType u) ++
        words ((P.bucket u).map encodeVertex)) := by
  simp only [table, List.map_map]
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, bucketPayload,
    BucketProgram.constructive_bucket_output P encodeType encodeVertex hinj]

/-- This is an actual finite-program trace returning the computed block count
and the exact ordered fiber table, not merely the existence of suitable blocks. -/
theorem typed_program_trace (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (suffix : List Bool) (regs : Fin 8 → Bool) :
    let records := BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex
    let keys := P.types.values.map encodeType
    ∃ n ≤ budget records keys, ∃ rf,
      BitProgram.Trace program n
        ((inputState records keys P.vertices.values.length suffix regs).withPC (some program.entry))
        ((PackingBucketCalls.state rf [] []
          (ProgramEncoding.encodeRecords (P.types.values.map (fun u => Encoding.frame (encodeType u) ++
            words ((P.bucket u).map encodeVertex))))
          (BucketProgram.encodeRecords records.reverse) suffix []
          (List.replicate P.blockCount true) [] [] []).withPC none) := by
  dsimp only
  have hlen : P.vertices.values.length ≤
      (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex).length := by
    simp [BucketProgram.vertexRecords]
  obtain ⟨n, hn, rf, ht⟩ := program_trace
    (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
    (P.types.values.map encodeType) P.vertices.values.length hlen suffix regs
  refine ⟨n, hn, rf, ?_⟩
  simpa only [outputState, minimum_eq_blockCount P encodeType encodeVertex hinj,
    table_eq_typed P encodeType encodeVertex hinj] using ht

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
