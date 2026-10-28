import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountDFS
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

/-! Physical space at an actual refined DFS boundary.

Raw clause order is retained in the serialized frontier. Normalized syntax
and the strictly ordered DFS depths bound that word; the count mass bounds
the canonical accumulator. The raw input, two setup words and every reserved
high port are charged independently of the semantic count invariant.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace

open SparseDFSRefinement SparseDFSBoundarySpace

variable {n : ℕ}

/-- The selected core and family retain at most the actual input body bytes.
This controls their physical padding and framing, not only their cardinality. -/
theorem selected_payload_lengths {k c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n)))
    (hcandidate : (c, H) ∈ SparsePriorityProgram.rawCandidates k F) :
    (Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode)).length ≤
        (SparseCountProgram.encodeBody F).length ∧
      (SparseCountProgram.encodeBody (SparsePriorityProgram.selectedRaw F c H)).length ≤
        (SparseCountProgram.encodeBody F).length := by
  obtain ⟨C, hC, _, hsub⟩ := SparsePriorityProgram.rawCandidate_spec k F c H hcandidate
  have hcore := EncodingLength.length_le_of_sublist Encoding.encodeNat
    (hsub.map Encoding.literalCode)
  have hmember := EncodingLength.length_le_of_sublist
    (Encoding.encodeList Encoding.encodeNat)
    ((List.singleton_sublist.mpr hC).map (List.map Encoding.literalCode))
  simp only [List.map_singleton, Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil] at hmember
  constructor
  · change _ ≤ (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (F.map (List.map Encoding.literalCode))).length
    omega
  · exact EncodingLength.length_le_of_sublist (Encoding.encodeList Encoding.encodeNat)
      (List.filter_sublist.map (List.map Encoding.literalCode))

/-- All three simultaneous splitter inputs are bounded by one retained body.
The actual branch program still charges every copied and framed child. -/
theorem selected_inputVolume_le {k c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n)))
    (hcandidate : (c, H) ∈ SparsePriorityProgram.rawCandidates k F) :
    ExecCoreChildProgram.inputVolume (F.map (List.map Encoding.literalCode))
      ((SparsePriorityProgram.selectedRaw F c H).map (List.map Encoding.literalCode))
      (H.map Encoding.literalCode) ≤ 4 * (SparseCountProgram.encodeBody F).length + 3 := by
  obtain ⟨hcore, hselected⟩ := selected_payload_lengths F H hcandidate
  change (SparseCountProgram.encodeBody (SparsePriorityProgram.selectedRaw F c H)).length +
    (SparseCountProgram.encodeBody F).length +
    2 * (Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode)).length + 3 ≤ _
  omega

theorem pendingBytes_length_le (pending : List (Node n)) (k depth : ℕ)
    (hlen : pending.length ≤ depth + 2)
    (hvalid : ∀ node ∈ pending, Valid k node.formula) :
    (pendingBytes pending).length ≤ frontierBound (SparseCountProgram.formulaBound n k) depth := by
  have hwords : ∀ node ∈ pending,
      (SparseCountProgram.encodeBody node.formula).length ≤ SparseCountProgram.formulaBound n k := by
    intro node hnode
    have hv := hvalid node hnode
    exact SparseCountProgram.encodeBody_length_le node.formula k hv.literal_nodup
      hv.clause_nodup (formulaSet_width_le node.formula hv.width)
  exact (Encoding.length_encodeList_upper
    (fun node : Node n => SparseCountProgram.encodeBody node.formula)
    pending (SparseCountProgram.formulaBound n k) hwords).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) 1)

/-- The full physical boundary bound covers every root port. In particular,
unused high ports do not disappear merely because the count refinement never
mentions them. Their concrete frame bound remains an explicit premise. -/
theorem boundary_stack_bound (M : List Bool) (s : Frontier n) (d : SparseDFSProgram.Data)
    (k depth rawBound dimensionBound parameterBound reservedBound : ℕ)
    (hboundary : Boundary M s d)
    (hlen : s.pending.length ≤ depth + 2)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula)
    (hcount : s.total ≤ 2 ^ n)
    (hraw : (d.stacks 256).length ≤ rawBound)
    (hdimension : (d.stacks 264).length ≤ dimensionBound)
    (hparameter : (d.stacks 266).length ≤ parameterBound)
    (hreserved : ∀ i : Fin 1220, 267 ≤ i.val → (d.stacks i).length ≤ reservedBound) :
    ∀ i, (d.stacks i).length ≤ storageBound (SparseCountProgram.formulaBound n k) depth
      (M.length + rawBound + dimensionBound + parameterBound + reservedBound) n := by
  have hpending := pendingBytes_length_le s.pending k depth hlen hvalid
  have htotal := binaryNat_length_le hcount
  intro i
  by_cases hlow : i.val < 256
  · rw [hboundary.low_empty i hlow]
    exact Nat.zero_le _
  by_cases hi256 : i = 256
  · subst i
    unfold storageBound
    omega
  by_cases hi257 : i = 257
  · subst i
    rw [hboundary.pending]
    unfold storageBound
    omega
  by_cases hi258 : i = 258
  · subst i
    rw [hboundary.header, Encoding.length_encodeNat]
    unfold storageBound
    omega
  by_cases hi259 : i = 259
  · subst i
    rw [hboundary.threshold]
    unfold storageBound
    omega
  by_cases hi260 : i = 260
  · subst i
    rw [hboundary.total]
    unfold storageBound
    omega
  by_cases hi261 : i = 261
  · subst i
    rw [hboundary.left_empty]
    exact Nat.zero_le _
  by_cases hi262 : i = 262
  · subst i
    rw [hboundary.right_empty]
    exact Nat.zero_le _
  by_cases hi263 : i = 263
  · subst i
    rw [hboundary.leaf_empty]
    exact Nat.zero_le _
  by_cases hi264 : i = 264
  · subst i
    unfold storageBound
    omega
  by_cases hi265 : i = 265
  · subst i
    rw [hboundary.current_empty]
    exact Nat.zero_le _
  by_cases hi266 : i = 266
  · subst i
    unfold storageBound
    omega
  have hi : 267 ≤ i.val := by
    simp only [Fin.ext_iff] at hi256 hi257 hi258 hi259 hi260 hi261 hi262 hi263 hi264 hi265 hi266
    omega
  have hr := hreserved i hi
  unfold storageBound
  omega

/-- Real semantic DFS transitions supply the count bound and the pending-list
ordering. Only node validity and their path-depth bound remain to be discharged
by the concrete refinement; no total visit-count bound is used for storage. -/
theorem reachable_boundary_stack_bound {k M visits : ℕ} {F : RawCNF n}
    {s : Frontier n} (d : SparseDFSProgram.Data) (threshold : List Bool)
    (depth rawBound dimensionBound parameterBound reservedBound : ℕ)
    (htrace : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ s)
    (hboundary : Boundary threshold s d)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula)
    (hdepth : ∀ node ∈ s.pending, node.depth ≤ depth)
    (hraw : (d.stacks 256).length ≤ rawBound)
    (hdimension : (d.stacks 264).length ≤ dimensionBound)
    (hparameter : (d.stacks 266).length ≤ parameterBound)
    (hreserved : ∀ i : Fin 1220, 267 ≤ i.val → (d.stacks i).length ≤ reservedBound) :
    ∀ i, (d.stacks i).length ≤ storageBound (SparseCountProgram.formulaBound n k) depth
      (threshold.length + rawBound + dimensionBound + parameterBound + reservedBound) n := by
  have hm : SparseCountProgram.Transitions visits
      (SparseCountProgram.initial (ExecCNF.formulaSet F)) s.model := htrace.model
  have hord := hm.ordered (.cons _ [] .nil (by simp))
  have hdepthModel : ∀ node ∈ s.model.pending, node.depth ≤ depth := by
    intro node hnode
    obtain ⟨raw, hrawNode, rfl⟩ := List.mem_map.mp hnode
    exact hdepth raw hrawNode
  have hlen := SparseCountProgram.ordered_length_le depth hord hdepthModel
  apply boundary_stack_bound threshold s d k depth rawBound dimensionBound parameterBound reservedBound
    hboundary _ hvalid (SparseCountProgram.Transitions.total_le_pow hm)
    hraw hdimension hparameter hreserved
  simpa only [Frontier.model, List.length_map] using hlen


/-- Starting from actual normalization, the semantic transition history
discharges both normalized-syntax validity and the path-depth premise. The
frontier depth is bounded by the original clause count times fixed width. -/
theorem normalized_reachable_boundary_space {k M visits : ℕ} {s : Frontier n}
    (F : RawCNF n) (d : SparseDFSProgram.Data) (threshold : List Bool)
    (rawBound dimensionBound parameterBound reservedBound : ℕ)
    (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (htrace : Transitions k M visits
      ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ s)
    (hboundary : Boundary threshold s d)
    (hraw : (d.stacks 256).length ≤ rawBound)
    (hdimension : (d.stacks 264).length ≤ dimensionBound)
    (hparameter : (d.stacks 266).length ≤ parameterBound)
    (hreserved : ∀ i : Fin 1220, 267 ≤ i.val → (d.stacks i).length ≤ reservedBound) :
    ∀ i, (d.stacks i).length ≤ storageBound (SparseCountProgram.formulaBound n k) (F.length * k)
      (threshold.length + rawBound + dimensionBound + parameterBound + reservedBound) n := by
  obtain ⟨hvalid, hdepth⟩ := htrace.normalized_pending_invariants F hM hwidth
  exact reachable_boundary_stack_bound d threshold (F.length * k)
    rawBound dimensionBound parameterBound reservedBound htrace hboundary hvalid hdepth
    hraw hdimension hparameter hreserved

/-- The real cleanup restores the smaller persistent boundary envelope after
a visit whose scratch workspace may use the larger transient envelope. The
bound depends on the normalized input and retained words, not on visits. -/
theorem finishVisit_reachable_boundary_space {k M visits : ℕ} {s : Frontier n}
    (F : RawCNF n) (d : SparseDFSProgram.Data) (threshold : List Bool)
    (transientBound rawBound dimensionBound parameterBound reservedBound : ℕ)
    (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (htrace : Transitions k M visits
      ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ s)
    (hvisit : AfterVisit threshold s d)
    (htransient : ∀ i, (d.stacks i).length ≤ transientBound)
    (hraw : (d.stacks 256).length ≤ rawBound)
    (hdimension : (d.stacks 264).length ≤ dimensionBound)
    (hparameter : (d.stacks 266).length ≤ parameterBound)
    (hreserved : ∀ i : Fin 1220, 267 ≤ i.val → (d.stacks i).length ≤ reservedBound) :
    ∃ t ≤ (2 * transientBound + 3) * 257 + 1, ∃ e,
      StructuredCalls.Eval SparseDFSProgram.finishVisit t d e ∧ Boundary threshold s e ∧
      (∀ i, (e.stacks i).length ≤ storageBound (SparseCountProgram.formulaBound n k) (F.length * k)
        (threshold.length + rawBound + dimensionBound + parameterBound + reservedBound) n) ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        BitProgram.Trace (StructuredCalls.compiled SparseDFSProgram.finishVisit 256 256)
          prefixSteps (d.withPC
            (some (StructuredCalls.compiled SparseDFSProgram.finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ transientBound := by
  obtain ⟨t, ht, e, he, hboundary, hframe, hspace⟩ :=
    finishVisit_boundary threshold s d transientBound hvisit htransient
  refine ⟨t, ht, e, he, hboundary, ?_, hframe, hspace⟩
  apply normalized_reachable_boundary_space F e threshold rawBound dimensionBound
    parameterBound reservedBound hM hwidth htrace hboundary
  · simpa only [hframe 256 (by decide) (by decide)] using hraw
  · simpa only [hframe 264 (by decide) (by decide)] using hdimension
  · simpa only [hframe 266 (by decide) (by decide)] using hparameter
  · intro i hi
    rw [hframe i (by omega) (by intro h; subst i; omega)]
    exact hreserved i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace
