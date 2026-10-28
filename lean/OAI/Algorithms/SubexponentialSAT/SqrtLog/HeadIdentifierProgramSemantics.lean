import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramTyped
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Position-major one-hot words are read at the paid runtime index t*r+g. -/
theorem encodeWord_getD {r Q : ℕ} (w : MulticolorTypes.Word r Q) (t : Fin Q) (g : Fin r) :
    (Subexp.ReadPlan.encodeWord w).getD (t.val*r+g.val) false=decide (w t=g) := by
  let f : Fin (Q*r) → Bool := fun i =>
    decide (w (finProdFinEquiv.symm i).1=(finProdFinEquiv.symm i).2)
  have he : List.ofFn f=(List.ofFn fun i : Fin Q =>
      List.ofFn fun j : Fin r => f (finProdFinEquiv (i,j))).flatten := by
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f
  have hf (i : Fin Q) (j : Fin r) : f (finProdFinEquiv (i,j))=decide (w i=j) := by
    change decide (w (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1=
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)=_
    rw [Equiv.symm_apply_apply]
  have he' : List.ofFn f=Subexp.ReadPlan.encodeWord w := by
    simpa only [hf,Subexp.ReadPlan.encodeWord] using he
  have hi : (finProdFinEquiv (t,g)).val=t.val*r+g.val := by
    simp [finProdFinEquiv]
    ring
  rw [← he',← hi]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using
    (finProdFinEquiv (t,g)).isLt)]
  simpa only [List.getElem_ofFn] using hf t g

def headRows {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q) : List (List Bool) :=
  List.ofFn (fun v => Subexp.ReadPlan.encodeWord (head v))

def lowBits {n : ℕ} (low : Fin n → Bool) : List Bool := List.ofFn low

theorem headRows_width {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q) :
    ∀ row ∈ headRows head,row.length=Q*r := by
  intro row hr
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
  simp [Subexp.ReadPlan.wordWidth]

theorem typed_predicate {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    predicate (headRows head) (lowBits low) (t.val*r+g.val) v.val=
      (low v && decide (head v t=g)) := by
  have hl : (lowBits low).getD v.val false=low v := by
    simp [lowBits,List.getD_eq_getElem?_getD]
  have hr : (headRows head).getD v.val []=Subexp.ReadPlan.encodeWord (head v) := by
    simp [headRows,List.getD_eq_getElem?_getD]
  rw [predicate,hl,hr,encodeWord_getD]

theorem chosenIds_bound (p : ℕ → Bool) (n : ℕ) : ∀ j ∈ chosenIds p n,j < n := by
  intro j hj
  exact List.mem_range.mp (List.mem_of_mem_filter hj)

theorem chosenIds_nodup (p : ℕ → Bool) (n : ℕ) : (chosenIds p n).Nodup :=
  (show (List.range n).Nodup from List.nodup_range).filter p

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

theorem encodedIds_length_bound (p : ℕ → Bool) (n : ℕ) :
    (HeadScatterProgram.indices (chosenIds p n)).length ≤ n*(2*n+2)+1 := by
  calc
    _ ≤ (chosenIds p n).length*(2*n+2)+1 :=
      HeadScatterProgram.indices_length_bound n _ (chosenIds_bound p n)
    _ ≤ n*(2*n+2)+1 := Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*n+2) (count_le p n)) 1

/-- Semantic naming of exactly the order already present in the emitted ID
stream; this definition does not perform an uncharged physical reindexing. -/
def headOrder (p : ℕ → Bool) (n : ℕ) (i : Fin (count p n)) : Fin n :=
  ⟨(chosenIds p n)[i.val],chosenIds_bound p n _ (List.getElem_mem i.isLt)⟩

theorem headOrder_injective (p : ℕ → Bool) (n : ℕ) : Function.Injective (headOrder p n) := by
  intro i j hij
  apply List.nodup_iff_injective_getElem.mp (chosenIds_nodup p n)
  exact congrArg Fin.val hij

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

theorem fullMasks_injective (p : ℕ → Bool) (n : ℕ) :
    Function.Injective (fun x : Fin (count p n) → Bool =>
      HeadScatterProgram.mask n (chosenIds p n) (HeadScatterProgram.headBits x)) := by
  simpa [headOrder_ids] using
    HeadScatterProgram.typed_mask_injective (headOrder p n) (headOrder_injective p n)

/-- Exact head membership, including uncovered low variables, in the original
ambient coordinate space. No packing-coverage condition is imposed. -/
theorem typed_chosen_mem {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val ∈ chosenIds (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n ↔
      low v=true ∧ head v t=g := by
  simp [chosenIds,typed_predicate,v.isLt]

/-- The output bytes are exactly the framed bare-unary ABI consumed by the
physical full-mask scatter; no encoding conversion or index permutation occurs. -/
theorem scatter_abi (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (result rows low W z).stacks 0 =
      HeadScatterProgram.indices (chosenIds (predicate rows low z) rows.length) := rfl

theorem typed_program_runsIn {n r Q : ℕ} (regs : Fin 16 → Bool)
    (head : Fin n → MulticolorTypes.Word r Q) (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    RunsIn program (budget n (Q*r) n (t.val*r+g.val))
      ((input regs (headRows head) (lowBits low) (Q*r) (t.val*r+g.val)).withPC (some program.entry))
      ((result (headRows head) (lowBits low) (Q*r) (t.val*r+g.val)).withPC none) := by
  simpa [headRows,lowBits] using program_runsIn regs (headRows head) (lowBits low)
    (Q*r) (t.val*r+g.val) (headRows_width head)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
