import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadOrder

/-! Exact physical words for the emitted numeric head representatives. These
are proof-level coordinate maps; the executable cursor retains only its bounded
binary word and uses the existing native selected-coordinate scan. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
open Classical
open OAI.Algorithms.SubexponentialSAT.SqrtLog

open BucketTupleProgram.Concrete HeadIdentifierProgram in
/-- The numeric representative word is exactly the selected ambient bits of
its source head assignment, in the physical loader's ascending coordinate
order. This includes an empty head and does not select a key representative
in a second, potentially different order. -/
theorem representative_selected_word {n r : ℕ}
    (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n,v.val∈chosenIds p n ↔ ∃ _ : v∉H,head v=g)
    (candidate : Fin (2^(chosenIds p n).length)) (current : Fin n → Bool)
    (hcurrent : ∀ (v : Fin n) (hv : v∉H) (hg : head v=g),
      current v=((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
          (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)) ⟨⟨v,hv⟩,hg⟩) :
    HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn current)=
      ExecCNFTupleEnumeration.fixedBits (chosenIds p n).length candidate.val := by
  rw [HeadRepresentativeSemantics.selected_headOrder,
    ←AttainedSignatures.assignment_word]
  apply congrArg List.ofFn
  funext i
  let order := freeOrder H (fun v => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs
  let rep := (freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
      (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)
  have he : (order i).val.val=headOrder p n i := by apply Fin.ext; rfl
  have hc := hcurrent (order i).val.val (order i).val.property (order i).property
  change current (order i).val.val=rep (order i) at hc
  have hr : rep (order i)=AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate i :=
    congrFun ((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs).apply_symm_apply
        (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)) i
  exact (he ▸ hc).trans hr

open BucketTupleProgram.Concrete HeadIdentifierProgram

/-- An ambient extension used only to identify the physical selected bits. -/
def ambientAssignment {n r : ℕ} (H : Finset (Fin n)) (head : Fin n → Fin r)
    (g : Fin r) (x : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool) :
    Fin n → Bool := fun v =>
  if hv : v∉H then if hg : head v=g then x ⟨⟨v,hv⟩,hg⟩ else false else false

theorem ambientAssignment_head {n r : ℕ} (H : Finset (Fin n)) (head : Fin n → Fin r)
    (g : Fin r) (x : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (v : Fin n) (hv : v∉H) (hg : head v=g) :
    ambientAssignment H head g x v=x ⟨⟨v,hv⟩,hg⟩ := by
  simp only [ambientAssignment, dite_eq_left hv, dite_eq_left hg]

/-- The actual numeric candidate supplies a concrete ambient extension whose
selected word is exactly the saved representative payload. -/
theorem emitted_word {n r : ℕ}
    (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n,v.val∈chosenIds p n ↔ ∃ _ : v∉H,head v=g)
    (candidate : Fin (2^(chosenIds p n).length)) :
    ExecCNFTupleEnumeration.fixedBits (chosenIds p n).length candidate.val=
      HighIncidenceProgram.Restriction.selected true
        (List.ofFn (fun v : Fin n => p v.val))
        (List.ofFn (ambientAssignment H head g
          ((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
            (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
              (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)))) :=
  (representative_selected_word H head g p hs candidate _
    (fun v hv hg => ambientAssignment_head H head g _ v hv hg)).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
