import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsFactors
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal

namespace OAI.Algorithms

/-! The source rows used by the native factor callback retain their concrete
origin, degree, and original-coordinate support after incidence pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly

variable {r Q d : ℕ}

abbrev universal (p : SourceBank.Parameters r Q d) :=
  LayoutUniversal.data (r:=r) p.aWord.length p.R p.denom p.hdenom
    (p.model.nodeUnits p.t Q p.ht p.hfield)

abbrev copied (p : SourceBank.Parameters r Q d) {D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  LayoutBlocks.data (universal p) P.completeBlocks id
    (fun i => (universal p).color (P.label i)) (fun _ _ => rfl)

theorem packed_origin (p : SourceBank.Parameters r Q d) {D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (i j : Fin D) :
    (packedValue P p.rows i j).eval 0 = if j=i then 1 else 0 := by
  rw [packedValue_eq]
  exact (copied p P).row_origin i j

theorem fixedSourceRow_degree (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) :
    (fixedSourceRow p ps P n f j v).natDegree ≤ p.R :=
  sourceRowFamily_degree ps n f j _ v.val p.R (totalPackedSource_degree p P)

theorem fixedSourceRow_zero (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) (hv : ∀ a ∈ ps, a.1 ≠ v.val) :
    fixedSourceRow p ps P n f j v = 0 := by
  unfold fixedSourceRow sourceRowFamily
  split_ifs
  · exact ownerSum_zero ps v.val _ hv
  · rfl

/-- Repeated incidences are allowed. The actual first matching lookup selects
one Kronecker row, whose owner is still the original literal. -/
theorem fixedSourceRow_origin (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) (hj : (j,n+f) ∈ ps) :
    (fixedSourceRow p ps P n f j v).eval 0 = if v.val=j then 1 else 0 := by
  let i : Fin ps.length := ⟨ps.idxOf (j,n+f), by
    simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr hj⟩
  have hi : ps.get i = (j,n+f) := by
    simpa only [i,List.idxOf,beq_eq_decide] using
      List.idxOf_get (List.idxOf_lt_length_iff.mpr hj)
  have hr : fixedSourceRow p ps P n f j v =
      LayoutPullback.row (fun a : Fin ps.length => (ps.get a).1)
        (fun a => packedValue P p.rows i a) v.val := by
    unfold fixedSourceRow
    rw [sourceRowFamily_present _ _ _ _ _ _ hj]
    have hs := ownerSum_pullback (fun a : Fin ps.length => ps.get a) v.val
      (totalPackedSource p P i.val)
    rw [List.ofFn_get] at hs
    rw [hs]
    congr 1
    funext a
    simp only [totalPackedSource,packedSourceValue,dite_eq_left i.isLt,dite_eq_left a.isLt]
  rw [hr]
  simp only [LayoutPullback.row,Polynomial.eval_finsetSum,apply_ite,
    Polynomial.eval_zero]
  simp_rw [packed_origin]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true,hi]
    by_cases hv : v.val=j
    · simp only [hv,ite_true]
    · have hv' : j ≠ v.val := Ne.symm hv
      simp only [hv,hv',ite_false]
  · intro a _ hai
    simp [hai]
  · simp

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
