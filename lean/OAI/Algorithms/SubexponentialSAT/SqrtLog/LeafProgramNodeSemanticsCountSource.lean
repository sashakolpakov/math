import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemantics

namespace OAI.Algorithms

/-! The recovered constant counts the original ternary row constraints.
The extension-ring residue test introduces no additional acceptance rule. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def ternaryAccepted (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) (x : V → Bool) : Prop :=
  (∀ ws∈hashes,rowValue (ringAlgebra (ZMod 3)) id
    (fun v => HashInput.boolValue (x v)) ws=0) ∧
  (marked=true → violates clause x=true)

def ternaryFixedHighCount (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V)) : ℕ :=
  ∑ x : ResidualEmbedding.Free H → Bool,
    if ternaryAccepted hashes marked clause (HighIncidence.glue H high x) then 1 else 0

omit [Fintype V] [DecidableEq V] in
theorem accepted_lifted_iff {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V))
    (x : V → Bool) :
    accepted (a.rho t ht) (liftedHashes a t hashes) marked clause x ↔
      ternaryAccepted hashes marked clause x := by
  classical
  unfold accepted ternaryAccepted
  apply and_congr_left
  intro _
  have hrow (ws : SparseRow V (ZMod 3)) :
      a.rho t ht (rowValue (ringAlgebra (a.O t)) id
        (fun v => HashInput.boolValue (x v))
        (ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2))))=0 ↔
      rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) ws=0 := by
    rw [rowValue_map_coeff]
    simp only [Function.id_comp]
    rw [TernaryLift.reduction_sparseRow a t ht]
    exact (LiftRing.of a.residuePolynomial).injective.eq_iff' (map_zero _)
  constructor
  · intro h ws hw
    apply (hrow ws).mp
    have hm : ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2))∈liftedHashes a t hashes :=
      List.mem_map.mpr ⟨ws,hw,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    simpa only [sourceHash,Fin.getElem_fin,he] using h ⟨i,hi⟩
  · intro h i
    have hm := List.getElem_mem i.isLt
    obtain ⟨ws,hw,he⟩ := List.mem_map.mp (show (liftedHashes a t hashes)[i]∈liftedHashes a t hashes from hm)
    change a.rho t ht (rowValue _ id _ (liftedHashes a t hashes)[i])=0
    rw [← he]
    exact (hrow ws).mpr (h ws hw)

theorem fixedHighCount_lifted {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (H : Finset V) (high : H → Bool) (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) :
    fixedHighCount (a.rho t ht) H high (liftedHashes a t hashes) marked clause =
      ternaryFixedHighCount H high hashes marked clause := by
  classical
  unfold fixedHighCount ternaryFixedHighCount
  simp only [accepted_lifted_iff]

theorem model_target_ternary_count {C : Type*} {d : ℕ} (a : RingModel.Data d)
    (t : ℕ) (ht : 0 < t)
    (ops : SubexpSymbolicCost.RepresentedRing C (ZMod (3^t)))
    (half : C) (hhalf : 2*ops.decode half=1)
    (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → Polynomial (a.O t))
    (horigin : ∀ i (v : ResidualEmbedding.Free H) w,
      (rows i v.val w).eval 0=if w=v then 1 else 0)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V)) :
    (target H t (computedDigits ops (a.base t) t half) (liftedHashes a t hashes) marked clause
      (branchPath H high rows)).eval 0 = (ternaryFixedHighCount H high hashes marked clause : a.O t) := by
  classical
  rw [model_target_origin a t ht ops half hhalf H high rows horigin hashes marked clause,
    fixedHighCount_lifted]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
