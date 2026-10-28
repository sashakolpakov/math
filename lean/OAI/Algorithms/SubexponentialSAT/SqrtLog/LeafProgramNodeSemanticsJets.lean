import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsBuckets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace OAI.Algorithms

/-! The actual dense readout and attained-bucket sum supply jets of the one
specified source target. The local bucket identity is kept explicit, so a
native parser or assignment service is never assumed to be correct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

variable {R : Type*} [CommRing R]

/-- U-polynomial before the one shared cutoff. Marking has U-degree zero. -/
def queryExpansion {V : Type*} (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) : Polynomial R[X] :=
  TotalOrder.fullProduct Finset.univ t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) *
      Polynomial.C (markedPath hashes marked clause path)

theorem queryExpansion_readout {V : Type*} (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) :
    Moments.sumUCoeff t (queryExpansion t digits hashes marked clause path) =
      queryPolynomial t digits hashes marked clause path := by
  unfold queryExpansion queryPolynomial
  rw [TotalOrder.output_eq_sum_coeff,Finset.sum_mul]
  simp only [Moments.sumUCoeff,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Polynomial.coeff_mul_C]

/-- Shifting T commutes with the retained U coefficient sum. -/
theorem shifted_readout (t : ℕ) (F : Polynomial R[X]) (theta : R) :
    Moments.sumUCoeff t (F.map (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X+Polynomial.C theta))) =
      (Moments.sumUCoeff t F).comp (Polynomial.X+Polynomial.C theta) := by
  simp only [Moments.sumUCoeff,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Polynomial.coeff_map]
  exact (map_sum (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X+Polynomial.C theta)) _ _).symm

theorem queryExpansion_shifted_readout {V : Type*} (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (theta : R) :
    Moments.sumUCoeff t ((queryExpansion t digits hashes marked clause path).map
      (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X+Polynomial.C theta))) =
      (queryPolynomial t digits hashes marked clause path).comp
        (Polynomial.X+Polynomial.C theta) := by
  rw [shifted_readout,queryExpansion_readout]

theorem sum_query_jets {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset V) (t J : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X]) (theta : R) :
    (∑ x, Truncation.trunc J ((queryPolynomial t digits hashes marked clause (path x)).comp
      (Polynomial.X+Polynomial.C theta))) =
      JetCRT.jet theta J (target H t digits hashes marked clause path) := by
  rw [TruncatedInverse.jet_eq_trunc]
  unfold target
  rw [Polynomial.sum_comp]
  exact (map_sum (Truncation.truncAddHom J) _ _).symm

section ActualReadout
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i*basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k))*basis k)
  (u J : ℕ)
  (meaning : MomentsAssembly.AssignmentContext → List Bool →
    MomentsAssembly.Contribution n (baseWidth p t) d)

/-- This is the dense list computed by the physical sparse coefficient scan. -/
theorem outputCodes_polynomial (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero=0) :
    PolynomialAlgorithm.denote ((MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J).map
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)) =
      MomentsAssembly.output p t M cache scalar basis u J entries := by
  rw [MomentsReadoutProgram.outputCodes_denote p t M cache scalar basis entries u J zero hn hz]
  rfl

include htable in
/-- The bucket hypothesis is exactly the conclusion supplied by the embedded
finite-bucket theorem after the assignment-product identity. -/
theorem actual_node_jet {G : Type*} [Fintype G] [DecidableEq G]
    (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → G)
    {L : G → Type*} [∀ g, DecidableEq (L g)]
    (label : ∀ g, (Moments.Head head g → Bool) → L g)
    (ys : List (∀ g, Moments.LabelValue label g)) (hyn : ys.Nodup)
    (hyc : ys.toFinset=Finset.univ)
    (input : (∀ g, Moments.LabelValue label g) → MomentsAssembly.BucketInput)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d))
    (ho : MomentsAssembly.denote p t M cache scalar basis one=Squarefree.canonical u J 1)
    (digits : Fin u → R[X]) (hashes : List (SparseRow (Fin n) R))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → Fin n → R[X]) (theta : R)
    (hb : ∀ y, MomentsAssembly.output p t M cache scalar basis u J
      (MomentsAssembly.supportsRun p t M cache table u J meaning
        (Function.update high 177 (input y).context) (input y).heads one ss []) =
      ∑ a : ∀ g, Moments.LabelBucket label g (y g),
        Truncation.trunc J ((queryPolynomial u digits hashes marked clause
          (path (Moments.assemble head (fun g => (a g).val)))).comp
            (Polynomial.X+Polynomial.C theta))) :
    MomentsAssembly.output p t M cache scalar basis u J
      (MomentsAssembly.bucketsRun p t M cache table u J meaning high ss one (ys.map input) []) =
      JetCRT.jet theta J (target H u digits hashes marked clause path) := by
  rw [MomentsAssembly.bucketsRun_output_boolean p t M cache scalar basis table htable
    u J meaning head label ys hyn hyc input
    (fun x => Truncation.trunc J ((queryPolynomial u digits hashes marked clause (path x)).comp
      (Polynomial.X+Polynomial.C theta))) high ss one ho hb]
  exact sum_query_jets H u J digits hashes marked clause path theta

end ActualReadout

/-- The source target is fixed in this statement; it cannot be replaced by
an unrelated polynomial merely satisfying a degree premise. -/
theorem hasJets_of_actual_outputs {C : Type*}
    (ops : SubexpSymbolicCost.RepresentedRing C R) {Q : ℕ}
    (nodes : Fin Q → C) (J : ℕ) (jets : Fin Q → List C)
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset V) (u : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X])
    (hj : ∀ i, PolynomialAlgorithm.denote ((jets i).map ops.decode) =
      JetCRT.jet (ops.decode (nodes i)) J (target H u digits hashes marked clause path)) :
    Reconstruction.HasJets ops nodes J jets (target H u digits hashes marked clause path) := by
  intro i
  rw [hj i,TruncatedInverse.jet_eq_trunc]
  ext k
  by_cases hk : k < J <;> simp [Truncation.coeff_trunc,hk]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
