import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramOrder
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRestrictionTotal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

/-- Exact meaning of repeated executions of the original ambient merge scan.
A head's supplied word need only agree with the target at its selected coordinates. -/
theorem merge_fold_ofFn {n : ℕ} {G : Type*} (heads : List G)
    (mask current : G → Fin n → Bool) (baseline target : Fin n → Bool)
    (hcurrent : ∀ g ∈ heads,∀ v,mask g v=true → current g v=target v) :
    heads.foldl (fun acc g => merge (List.ofFn (current g)) (List.ofFn (mask g)) acc)
        (List.ofFn baseline) =
      List.ofFn (fun v => if heads.any (fun g => mask g v) then target v else baseline v) := by
  induction heads generalizing baseline with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons,merge_ofFn]
    rw [ih _ (fun h hh => hcurrent h (by simp [hh]))]
    apply congrArg List.ofFn
    funext v
    have hg := hcurrent g (by simp) v
    cases hm : mask g v <;> cases ht : gs.any (fun h => mask h v) <;>
      simp only [List.any_cons, hm, ht, Bool.or_false, Bool.or_true, Bool.false_eq_true,
        ite_true, ite_false]
    exact hg hm

/-- All representative heads reconstruct the full ambient assignment, with
fixed-high coordinates retained. Head order and repeated visits are harmless. -/
theorem representative_heads {n : ℕ} {G : Type*} [DecidableEq G]
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → G)
    (reps : ∀ g,Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (heads : List G) (hcover : ∀ g,g∈heads) (current : G → Fin n → Bool)
    (hcurrent : ∀ g ∈ heads,∀ v (hv : v∉H) (hg : head v=g),
      current g v=reps g ⟨⟨v,hv⟩,hg⟩) :
    heads.foldl (fun acc g => merge (List.ofFn (current g))
        (List.ofFn (fun v => decide (v∉H ∧ head v=g))) acc)
        (List.ofFn (HighIncidence.glue H high (fun _ => false))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps)) := by
  classical
  rw [merge_fold_ofFn heads _ _ _
    (HighIncidence.glue H high (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps))]
  · apply congrArg List.ofFn
    funext v
    by_cases hv : v∈H
    · have hm : heads.any (fun g => decide (v∉H ∧ head v=g))=false := by simp [hv]
      simp [HighIncidence.glue, hv]
    · have hm : heads.any (fun g => decide (v∉H ∧ head v=g))=true := by
        apply List.any_eq_true.mpr
        exact ⟨head v,hcover (head v),by simp [hv]⟩
      simp only [hm, ite_true]
  · intro g hg v hv
    have hm : v∉H ∧ head v=g := of_decide_eq_true hv
    rw [hcurrent g hg v hm.1 hm.2]
    simp only [HighIncidence.glue, dite_eq_right hm.1, Moments.assemble]
    have hg := hm.2
    subst g
    rfl

/-- Updating the owned head in the reconstructed representative preserves
all foreign-head bits, including fixed-high coordinates. -/
theorem merge_candidate_ofFn {n : ℕ} {G : Type*} [DecidableEq G]
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → G)
    (reps : ∀ g,Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (g : G) (candidate : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (current : Fin n → Bool)
    (hcurrent : ∀ v (hv : v∉H) (hg : head v=g),current v=candidate ⟨⟨v,hv⟩,hg⟩) :
    merge (List.ofFn current) (List.ofFn (fun v => decide (v∉H ∧ head v=g)))
      (List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val)
          (Function.update reps g candidate))) := by
  rw [merge_ofFn]
  apply congrArg List.ofFn
  funext v
  by_cases hv : v∈H
  · simp [hv,HighIncidence.glue]
  · by_cases hg : head v=g
    · subst g
      simp [hv,HighIncidence.glue,Moments.assemble,hcurrent v hv rfl]
    · simp [hv,hg,HighIncidence.glue,Moments.assemble]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HeadIdentifierProgram
open HighIncidenceProgram

/-- The actual chosen-ID word fixes the ascending selection order. -/
theorem headOrder_stream (p : ℕ → Bool) (n : ℕ) :
    (List.finRange n).filter (fun v => p v.val)=List.ofFn (headOrder p n) := by
  apply (List.map_injective_iff.mpr (Fin.val_injective : Function.Injective (Fin.val (n:=n))))
  rw [List.map_ofFn]
  change _=HeadScatterProgram.headIds (headOrder p n)
  rw [headOrder_ids]
  simpa only [List.map_coe_finRange,chosenIds,Function.comp_def] using
    (List.filter_map (f:=(Fin.val : Fin n → ℕ)) (p:=p) (l:=List.finRange n)).symm

/-- The native selected-bit scan emits exactly the current head's ambient
coordinates in the already emitted headOrder, including the empty head. -/
theorem selected_headOrder (p : ℕ → Bool) (n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn x) =
      List.ofFn (fun i => x (headOrder p n i)) := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,Order.selected_map,headOrder_stream,List.map_ofFn]
  rfl

/-- The physical selected-mask population is the actual emitted head width. -/
theorem headOrder_highCount (p : ℕ → Bool) (n : ℕ) :
    Restriction.highCount (List.ofFn (fun v : Fin n => p v.val))=count p n := by
  have hh := Restriction.selected_true_length (List.ofFn (fun v : Fin n => p v.val))
    (List.ofFn (fun _ : Fin n => true)) (by simp)
  rw [selected_headOrder,List.length_ofFn] at hh
  exact hh.symm

/-- The concrete local correction word is the support indicator at the
same ascending head positions used by the cursor and full matrix columns. -/
theorem selected_supportBits (p : ℕ → Bool) (n : ℕ) (E : Finset (Fin n)) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩) =
      LeafWeightProgram.supportBits
        ⟨Finset.univ.filter (fun i => headOrder p n i∈E)⟩ := by
  rw [LeafWeightProgram.supportBits,selected_headOrder]
  simp [LeafWeightProgram.supportBits]

/-- Combined with NativeHeadSelect.prepared_E/prepared_H, this identifies
the actual gate test with membership in E at original head coordinates. -/
theorem head_correction_iff (p : ℕ → Bool) (n : ℕ) (E : Finset (Fin n))
    (bits : Fin (count p n) → Bool) :
    LeafWeightProgram.good (List.ofFn bits)
      (Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩)) (List.replicate (count p n) true)=true ↔
      ∀ i,headOrder p n i∈E → bits i=true := by
  rw [LeafWeightProgram.supportBits,selected_headOrder,
    ←List.ofFn_const,LeafWeightProgram.good_ofFn_iff]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
