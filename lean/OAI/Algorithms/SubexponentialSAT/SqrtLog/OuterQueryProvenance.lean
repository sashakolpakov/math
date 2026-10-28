import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput

namespace OAI.Algorithms

/-! The literal source words and semantic/resource origin of every reached
mass trial and accepted-count query. Native staging still performs the
copies; the final lemmas identify its resulting words without a new oracle. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafScopeResourceBounds
open LeafOuterProgram

noncomputable section

structure MasterWords (q : LeafQueryFrontend.Query) (a : Data) : Prop where
  formula : a.stacks 784=Encoding.encodeList id q.clauses
  modulus : a.stacks 782=q.modulus
  width : a.stacks 783=q.width
  ambient : a.stacks 785=q.ambient

structure TrialWords (q : LeafQueryFrontend.Query) (a : Data) : Prop extends MasterWords q a where
  rows : true::(Encoding.frame (a.stacks 768).reverse ++ a.stacks 777)=
    HashScopeProgram.RawTable.inputBits q.width.length q.rows

structure FinalWords (q : LeafQueryFrontend.Query) (a : Data) : Prop extends MasterWords q a where
  rows : a.stacks 777=HashScopeProgram.RawTable.inputBits q.width.length q.rows

theorem trial_provenance {n k B : ℕ} (F : Formula n) (a frame current : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F))
    (hn : 0 < n) (hm : 0 < (formulaRecords F).length) (hk : ∀ C ∈ F, C.length ≤ k)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (round : ℕ) (hround : round < HashSelect.loopCap n (formulaRecords F).length)
    (hf : Execution.Hash.ContextFrame selector a frame)
    (hr : ControllerReady selector.controller frame (seed::rest)
      (selected score seed rest (initial F a s Q) round) current)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool)
    (hb : bits ∈ seed::rest) (mark : Option (Fin (formulaRecords F).length)) :
    let q := query F a (trialRows F a hm s Q score seed rest round bits) mark
    q.Valid ∧ ProducedQueryResources.ambient q=n ∧
      Nonempty (ProducedQueryResources.Origin q k B) ∧
      TrialWords q (massInput current regs bits best queue) := by
  refine ⟨query_valid F a ha hm hn _ _,query_ambient F a ha _ _,
    ⟨trial_origin F a ha hm hk s Q score seed rest hfamily round hround.le bits hb mark⟩,?_⟩
  constructor
  · constructor
    · exact (massInput_outer hf hr regs bits best queue 784 (by omega)).trans hformula
    · exact massInput_outer hf hr regs bits best queue 782 (by omega)
    · exact massInput_outer hf hr regs bits best queue 783 (by omega)
    · exact massInput_outer hf hr regs bits best queue 785 (by omega)
  · exact massInput_trial_bytes F a frame current ha hm s Q score seed rest hfamily
      round hr regs bits best queue hb

theorem final_provenance {n k B : ℕ} (F : Formula n) (a b : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F))
    (hn : 0 < n) (hm : 0 < (formulaRecords F).length) (hk : ∀ C ∈ F, C.length ≤ k)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (hf : Execution.Hash.ContextFrame selector a b)
    (hrows : b.stacks 777=candidateEncoding (selected score seed rest (initial F a s Q)
      (HashSelect.loopCap n (formulaRecords F).length)))
    (mark : Option (Fin (formulaRecords F).length)) :
    let q := query F a (finalRows F a hm s Q score seed rest) mark
    q.Valid ∧ ProducedQueryResources.ambient q=n ∧
      Nonempty (ProducedQueryResources.Origin q k B) ∧ FinalWords q b := by
  refine ⟨query_valid F a ha hm hn _ _,query_ambient F a ha _ _,
    ⟨final_origin F a ha hm hk s Q score seed rest hfamily mark⟩,?_⟩
  constructor
  · constructor
    · exact (selected_outer_frame hf 784 (by decide)).trans hformula
    · exact selected_outer_frame hf 782 (by decide)
    · exact selected_outer_frame hf 783 (by decide)
    · exact selected_outer_frame hf 785 (by decide)
  · exact hrows.trans (final_encoding F a ha hm s Q score seed rest hfamily)

/-- Discharge the native source predicate from the actual copied words. -/
theorem TrialWords.staged {q : LeafQueryFrontend.Query} {a : Data}
    (h : TrialWords q a) (b : LeafProgram.Query.Data)
    (hf : b.stacks 700=a.stacks 784)
    (hr : b.stacks 701=true::(Encoding.frame (a.stacks 768).reverse ++ a.stacks 777))
    (hm : b.stacks 707=a.stacks 782) (hw : b.stacks 708=a.stacks 783)
    (hn : b.stacks 709=a.stacks 785) : LeafProgram.Query.Sources q b :=
  ⟨hf.trans h.formula,hr.trans h.rows,hm.trans h.modulus,hw.trans h.width,hn.trans h.ambient⟩

theorem FinalWords.staged {q : LeafQueryFrontend.Query} {a : Data}
    (h : FinalWords q a) (b : LeafProgram.Query.Data)
    (hf : b.stacks 700=a.stacks 784) (hr : b.stacks 701=a.stacks 777)
    (hm : b.stacks 707=a.stacks 782) (hw : b.stacks 708=a.stacks 783)
    (hn : b.stacks 709=a.stacks 785) : LeafProgram.Query.Sources q b :=
  ⟨hf.trans h.formula,hr.trans h.rows,hm.trans h.modulus,hw.trans h.width,hn.trans h.ambient⟩

end
end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
