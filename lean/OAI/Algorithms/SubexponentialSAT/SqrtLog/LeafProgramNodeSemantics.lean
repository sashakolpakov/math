import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsBucket

namespace OAI.Algorithms

/-! Public source-specific facts for the native node/count join. The target,
its degree, and its exact constant count all refer to the same polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

/-- Actual original-ID layout rows give the required source origin, and the
integer lifts give the required prime-subfield residues automatically. -/
theorem model_target_origin {C V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (ops : SubexpSymbolicCost.RepresentedRing C (ZMod (3^t)))
    (half : C) (hhalf : 2*ops.decode half=1)
    (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → Polynomial (a.O t))
    (horigin : ∀ i (v : ResidualEmbedding.Free H) w,
      (rows i v.val w).eval 0 = if w=v then 1 else 0)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V)) :
    (target H t (computedDigits ops (a.base t) t half) (liftedHashes a t hashes) marked clause
      (branchPath H high rows)).eval 0 =
      (fixedHighCount (a.rho t ht) H high (liftedHashes a t hashes) marked clause : a.O t) := by
  classical
  apply target_origin ops (a.base t) (a.rho t ht) 3 t (a.prime_power_zero t)
    (fun y hy => (a.rho_eq_zero_iff t ht y).mp hy) half hhalf
  · exact branchPath_origin H high rows horigin
  · intro x i
    exact liftedHashes_residue a t ht hashes (HighIncidence.glue H high x) i

/-- The sparse source width bound survives coefficient lifting verbatim. -/
theorem liftedHashes_width {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t k : ℕ) (hashes : List (SparseRow V (ZMod 3)))
    (hw : ∀ ws∈hashes,∀ w∈ws,w.2.length ≤ k) :
    ∀ ws∈liftedHashes a t hashes,∀ w∈ws,w.2.length ≤ k := by
  intro ws hws w hw'
  obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hws
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw'
  exact hw ls hls v hv

/-- This degree bound is attached to the same code-derived source polynomial
whose constant coefficient is identified by model_target_origin. -/
theorem model_target_degree {C V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t : ℕ)
    (ops : SubexpSymbolicCost.RepresentedRing C (ZMod (3^t))) (half : C)
    (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → Polynomial (a.O t))
    (k r Q factors : ℕ) (hQ : 0 < Q)
    (hrows : ∀ i v w,(rows i v w).natDegree ≤ r)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V))
    (hwidth : ∀ ws∈hashes,∀ w∈ws,w.2.length ≤ k) (hclause : clause.length ≤ k)
    (hfactors : hashes.length ≤ factors) :
    (target H t (computedDigits ops (a.base t) t half) (liftedHashes a t hashes) marked clause
      (branchPath H high rows)).natDegree <
        Q*Reconstruction.jetOrder (Reconstruction.markedDegreeBound k r factors t) Q := by
  apply branch_target_degree_lt H high rows t k r Q factors hQ hrows _
    (computedDigits_degree ops (a.base t) t half) _ marked clause
    (liftedHashes_width a t k hashes hwidth) hclause
  simpa [liftedHashes] using hfactors

/-- The generic count reader's ambient bound follows from summing only free
assignments. The multiplicity m is the outer query allowance. -/
theorem model_count_bound {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (H : Finset V) (high : H → Bool) (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) (m : ℕ) (hm : 1 ≤ m) :
    fixedHighCount (a.rho t ht) H high (liftedHashes a t hashes) marked clause ≤
      m*2^Fintype.card V := by
  classical
  apply (fixedHighCount_le (a.rho t ht) H high _ marked clause).trans
  have hc : Fintype.card (ResidualEmbedding.Free H) ≤ Fintype.card V :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  calc
    2^Fintype.card (ResidualEmbedding.Free H) ≤ 2^Fintype.card V := Nat.pow_le_pow_right (by decide) hc
    _ ≤ m*2^Fintype.card V := by simpa using Nat.mul_le_mul_right (2^Fintype.card V) hm

/-- Concrete native outputCodes, rather than an arbitrary list decoder,
provide the reconstruction jets once the node bucket theorem is applied. -/
theorem actual_dense_hasJets {R : Type*} [CommRing R]
    (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d Q : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R) (u J : ℕ)
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word (baseWidth p t)) d) R)
    (hdecode : ops.decode=RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
    (nodes : Fin Q → RingProgram.Code (Word (baseWidth p t)) d)
    (entries : Fin Q → List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : ∀ i,(Squarefree.Sparse.keys (entries i)).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero=0)
    (H : Finset (Fin n)) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → Fin n → R[X])
    (hnode : ∀ i,MomentsAssembly.output p t M cache scalar basis u J (entries i)=
      JetCRT.jet (ops.decode (nodes i)) J (target H u digits hashes marked clause path)) :
    Reconstruction.HasJets ops nodes J
      (fun i => MomentsReadoutProgram.outputCodes p t M cache (entries i) u zero 0 J)
      (target H u digits hashes marked clause path) := by
  apply hasJets_of_actual_outputs ops nodes J _ H u digits hashes marked clause path
  intro i
  rw [hdecode,outputCodes_polynomial p t M cache scalar basis u J (entries i) zero (hn i) hz]
  simpa only [hdecode] using hnode i

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
