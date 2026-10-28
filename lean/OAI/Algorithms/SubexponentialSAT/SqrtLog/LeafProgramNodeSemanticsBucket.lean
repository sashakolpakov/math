import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingIncidence

namespace OAI.Algorithms

/-! The ambient sparse execution is transported to free variables before
finite moment extraction. Its assignment enumeration is never enlarged. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i*basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k))*basis k)
  (u J : ℕ)
  (meaning : MomentsAssembly.AssignmentContext → List Bool →
    MomentsAssembly.Contribution n (baseWidth p t) d)

include htable in
/-- Its hlocal premise is supplied by the actual assignment contribution
semantics. hquery is the colored-product theorem after source substitution. -/
theorem embedded_bucket_query
    (H : Finset (Fin n)) {G : Type*} [Fintype G] [DecidableEq G]
    {X : G → Type*} [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
    (gs : List G) (xs : ∀ g,List (X g)) (input : G → MomentsAssembly.HeadInput)
    (encode : ∀ g,X g → List Bool)
    (hxs : ∀ g,(input g).assignments=(xs g).map (encode g))
    {vars : Finset (Fin n)}
    (D : ∀ g,X g → Moments.Stored (R:=R) vars u J)
    (F : ∀ g,X g → Moments.Stored (R:=R) (Finset.univ : Finset (ResidualEmbedding.Free H)) u J)
    (w : Finset (Fin n) → ∀ g,X g → R)
    (wf : Finset (ResidualEmbedding.Free H) → ∀ g,X g → R)
    (hD : ∀ g x,(D g x).denote=ResidualEmbedding.jet (ResidualEmbedding.inclusion H) (F g x).denote)
    (hw : ∀ s g x,w (s.map (ResidualEmbedding.inclusion H)) g x=wf s g x)
    (hgs : gs.Nodup) (hgc : gs.toFinset=Finset.univ)
    (hxn : ∀ g,(xs g).Nodup) (hxc : ∀ g,(xs g).toFinset=Finset.univ)
    (high : Fin 768 → List Bool) (one : List (Product.Entry n (baseWidth p t) d))
    (ss : List (Finset (Fin n))) (fs : List (Finset (ResidualEmbedding.Free H)))
    (hs : ss.Nodup) (hf : fs.Nodup)
    (hmem : ∀ s,s.map (ResidualEmbedding.inclusion H)∈ss ↔ s∈fs)
    (hM : ∀ s : Finset (ResidualEmbedding.Free H),s.card < J → s∈fs)
    (ho : MomentsAssembly.denote p t M cache scalar basis one=Squarefree.canonical u J 1)
    (hlocal : ∀ s∈ss,∀ g∈gs,∀ x∈xs g,
      MomentsAssembly.contributionDenote p t M cache scalar basis
        (meaning (MomentsAssembly.headContext (Function.update high 168 (Squarefree.encodeMask s))
          (input g)) (encode g x)) = Moments.ringScalar (w s g x)*(D g x).denote)
    (assignment : (∀ g,X g) → ResidualEmbedding.Free H → Bool)
    (hweight : ∀ s x,Moments.jetConstant (Squarefree.weight
      (Squarefree.boolValue (R:=R) (assignment x)) s)=
        ∏ g,Moments.jetConstant (wf s g (x g)))
    (digits : Fin u → R[X]) (hashes : List (SparseRow (Fin n) R))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → Fin n → R[X]) (theta : R)
    (hquery : ∀ x,Truncation.trunc J (Moments.sumUCoeff u
      (Moments.jetEval (Squarefree.boolValue (assignment x))
        (Squarefree.boolValue_idempotent (assignment x)) (∏ g,(F g (x g)).denote))) =
      Truncation.trunc J ((queryPolynomial u digits hashes marked clause (path (assignment x))).comp
        (Polynomial.X+Polynomial.C theta))) :
    MomentsAssembly.output p t M cache scalar basis u J
      (MomentsAssembly.supportsRun p t M cache table u J meaning high (gs.map input) one ss []) =
      ∑ x,Truncation.trunc J ((queryPolynomial u digits hashes marked clause (path (assignment x))).comp
        (Polynomial.X+Polynomial.C theta)) := by
  rw [MomentsAssembly.output,
    MomentsAssembly.supportsRun_embedded_finite_bucket p t M cache scalar basis table htable u J
      meaning gs xs input encode hxs D w high (ResidualEmbedding.inclusion H) F wf hD hw
      hgs hgc hxn hxc one ss fs hs hf hmem hM ho hlocal
      (fun x => Squarefree.boolValue (assignment x))
      (fun x => Squarefree.boolValue_idempotent (assignment x)) hweight]
  exact Finset.sum_congr rfl (fun x _ => hquery x)

/-- The product bridge may be stated at the actual ambient IDs; this lemma
transports its final readout to the free moment calculation exactly. -/
theorem embedded_product_readout (H : Finset (Fin n)) (fixed : H → Bool)
    {G : Type*} [Fintype G] (D : G → Squarefree.Jet (Fin n) R)
    (F : G → Squarefree.Jet (ResidualEmbedding.Free H) R)
    (hD : ∀ g,D g=ResidualEmbedding.jet (ResidualEmbedding.inclusion H) (F g))
    (x : ResidualEmbedding.Free H → Bool) :
    Truncation.trunc J (Moments.sumUCoeff u
      (Moments.jetEval (Squarefree.boolValue (HighIncidence.glue H fixed x))
        (Squarefree.boolValue_idempotent (HighIncidence.glue H fixed x)) (∏ g,D g))) =
    Truncation.trunc J (Moments.sumUCoeff u
      (Moments.jetEval (Squarefree.boolValue x)
        (Squarefree.boolValue_idempotent x) (∏ g,F g))) := by
  simp_rw [hD]
  rw [← map_prod,ResidualEmbedding.eval_jet_branch]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
