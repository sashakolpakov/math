import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStep
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSupport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramSemantics

namespace OAI.Algorithms

/-! The head mask and factor context are read from the actual assignment
controller's output. Distinct head colors give disjoint ambient masks. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT MulticolorTypes

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

theorem source_head_index (v : Fin n) :
    LocalExpectation.indexCode (LeafHeadFactorsProgram.indices n N) (.inl v)=v.val := by
  unfold LeafHeadFactorsProgram.indices
  rw [Packing.headsFirst_index_head _ _ _ (by simp)]
  simp [LocalExpectation.indexCode]

omit [DecidableEq I] in
theorem source_head_row (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator) (v : Fin n) :
    (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w).getD v.val []=
      Subexp.ReadPlan.encodeWord
        (Packing.computedWords owner factor a tail terms (LeafHeadFactorsProgram.indices n N) x y (.inl v)) := by
  let values := PackingProgram.selectedValues owner factor a tail terms
    (LeafHeadFactorsProgram.indices n N) w
  have hlen : values.length=n+N := by
    simp [values,PackingProgram.selectedValues,LeafHeadFactorsProgram.assignNat_length]
  have hv : v.val < values.reverse.length := by
    rw [List.length_reverse,hlen]
    omega
  have he := congrFun (PackingProgram.selectedValues_eq_computedWords
    owner factor a tail terms (LeafHeadFactorsProgram.indices n N) w x y hy hx) (.inl v)
  rw [source_head_index,Subexp.AssignmentEnumeration.decode_eq_reverse_getD,
    List.getD_eq_getElem _ _ hv] at he
  unfold LeafHeadFactorsProgram.sourceRows
  change (values.reverse.map Subexp.ReadPlan.encodeWord).getD v.val []=_
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hv),List.getElem_map,he]

omit [DecidableEq I] in
theorem source_head_predicate (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    HeadIdentifierProgram.predicate
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val) v.val=
      (low v && decide (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g)) := by
  unfold HeadIdentifierProgram.predicate
  rw [source_head_row owner factor a tail terms w x y hy hx v,
    HeadIdentifierProgram.encodeWord_getD]
  simp [HeadIdentifierProgram.lowBits,List.getD_eq_getElem?_getD]

omit [DecidableEq I] in
theorem selectedMask_source (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    selectedMask n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)=
      List.ofFn (fun v : Fin n => low v && decide
        (Packing.computedWords owner factor a tail terms
          (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g)) := by
  change HeadScatterProgram.mask n _ (List.replicate
    (HeadIdentifierProgram.count _ n) true)=_
  unfold selectedHeads
  rw [HeadIdentifierProgram.support_mask_eq]
  congr 1
  funext v
  exact source_head_predicate owner factor a tail terms w x y hy hx low t g v

omit [DecidableEq I] in
theorem selectedHeads_source_mem (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val∈selectedHeads n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val) ↔
      low v=true ∧ Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g := by
  simp [selectedHeads,HeadIdentifierProgram.chosenIds,v.isLt,
    source_head_predicate owner factor a tail terms w x y hy hx low t g v]

omit [DecidableEq I] in
theorem selectedMasks_source_disjoint (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g h : Fin r) (hne : g≠h) (j : ℕ) :
    ¬ ((selectedMask n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
        (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)).getD j false=true ∧
      (selectedMask n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
        (HeadIdentifierProgram.lowBits low) (t.val*r+h.val)).getD j false=true) := by
  rw [selectedMask_source owner factor a tail terms w x y hy hx low t g,
    selectedMask_source owner factor a tail terms w x y hy hx low t h]
  by_cases hj : j < n
  · have hread (f : Fin n → Bool) : (List.ofFn f).getD j false=f ⟨j,hj⟩ := by
      simp [List.getD_eq_getElem?_getD,hj]
    rw [hread,hread]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    rintro ⟨hg,hh⟩
    exact hne (hg.2.symm.trans hh.2)
  · simp [List.getD_eq_getElem?_getD,hj]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
