import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramFinal

namespace OAI.Algorithms

/-! The target uses the actual binary Newton coefficient array. Its constant
and degree statements do not replace it by a separate coefficient algorithm. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def binaryDigits (p : SourceBank.Parameters r Q d)
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) : Fin p.t → Polynomial (p.model.O p.t) :=
  fun s => (IdempotentProgram.digitPolynomial (RingProgram.scalarRing 3 p.t M cache)
    (IdempotentProgram.binaryLiftWords p.t M cache half) s).map (p.model.base p.t)

theorem binaryDigits_eq_code (p : SourceBank.Parameters r Q d)
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t)
    (ctx : IdempotentApplyProgram.Steps.Context 3 p.t n d) :
    binaryDigits p M cache half = NodeSemantics.codeDigits ctx (p.model.base p.t)
      (IdempotentProgram.binaryLiftWords p.t M cache half) := by
  rfl

theorem binaryDigits_degree (p : SourceBank.Parameters r Q d)
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (s : Fin p.t) :
    (binaryDigits p M cache half s).natDegree ≤ 2 := by
  apply Polynomial.natDegree_map_le.trans
  have h := IdempotentProgram.digitPolynomial_degree (RingProgram.scalarRing 3 p.t M cache)
    (IdempotentProgram.binaryLiftWords p.t M cache half) s
  omega

def binaryTarget (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) : Polynomial (p.model.O p.t) :=
  NodeSemantics.target H p.t (binaryDigits p M cache half)
    (NodeSemantics.liftedHashes p.model p.t hashes) marked clause
    (NodeSemantics.branchPath H high (completedRows p ps P H))

theorem binaryTarget_count (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (hhalf : 2*wordValue 3 p.t half=1)
    (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    (binaryTarget p ps P M cache half H high hashes marked clause).eval 0 =
      (NodeSemantics.ternaryFixedHighCount H high hashes marked clause : p.model.O p.t) := by
  classical
  rw [← NodeSemantics.fixedHighCount_lifted p.model p.t p.ht H high hashes marked clause]
  simp only [binaryTarget,NodeSemantics.target,Polynomial.eval_finsetSum,
    NodeSemantics.fixedHighCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply NodeSemantics.queryPolynomial_origin (p.model.rho p.t p.ht) 3 p.t
    (p.model.prime_power_zero p.t)
    (fun y hy => (p.model.rho_eq_zero_iff p.t p.ht y).mp hy)
  · exact NodeSemantics.branchPath_origin H high (completedRows p ps P H)
      (completedRows_origin p ps P H) x
  · intro i
    exact NodeSemantics.liftedHashes_residue p.model p.t p.ht hashes
      (HighIncidence.glue H high x) i
  · intro i
    simpa only [binaryDigits,Polynomial.eval_map] using
      IdempotentProgram.binaryLiftWords_indicator p.t M cache half hhalf
        (p.model.base p.t) (p.model.rho p.t p.ht) 3 (p.model.prime_power_zero p.t)
        (fun y hy => (p.model.rho_eq_zero_iff p.t p.ht y).mp hy)
        (NodeSemantics.sourceHash (NodeSemantics.liftedHashes p.model p.t hashes)
          (HighIncidence.glue H high x) i)
        (NodeSemantics.liftedHashes_residue p.model p.t p.ht hashes
          (HighIncidence.glue H high x) i)

theorem binaryTarget_degree (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (k factors : ℕ) (hQ : 0 < Q)
    (hwidth : ∀ ws∈hashes,∀ w∈ws,w.2.length ≤ k) (hclause : clause.length ≤ k)
    (hfactors : hashes.length ≤ factors) :
    (binaryTarget p ps P M cache half H high hashes marked clause).natDegree <
      Q*Reconstruction.jetOrder (Reconstruction.markedDegreeBound k p.R factors p.t) Q := by
  apply NodeSemantics.branch_target_degree_lt H high (completedRows p ps P H)
    p.t k p.R Q factors hQ (completedRows_degree p ps P H) _
    (binaryDigits_degree p M cache half) _ marked clause
    (NodeSemantics.liftedHashes_width p.model p.t k hashes hwidth) hclause
  simpa only [NodeSemantics.liftedHashes,List.length_map] using hfactors

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
