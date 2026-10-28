import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyRelSemanticsFinite

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}
  (u J : ℕ) (semantic : AssignmentContext → List Bool → Jet (Fin n) R)

/-- This identity is independent of raw execution witnesses. -/
theorem bucketDenotation_eq_run {vars : Finset (Fin n)}
    (bucket : List Bool) (hs : List HeadInput) (ss : List (Finset (Fin n)))
    (data : Finset (Fin n) → List (List (R × Moments.Stored (R:=R) vars u J)))
    (hd : ∀ s∈ss,(hs.map (headValue semantic (encodeMask s) bucket))=
      ((data s).map fun l => (l.map fun a => Moments.ringScalar a.1*a.2.denote).sum)) :
    bucketDenotation u J semantic ss ⟨bucket,hs⟩=
      Moments.Stored.denote (MomentsAlgorithm.run Moments.Stored.ops data ss).1 := by
  rw [MomentsAlgorithm.run_canonical
    (Moments.Stored.ops (R:=R) (vars:=vars) (t:=u) (J:=J))
    Moments.Stored.denote (Moments.ringScalar (V:=Fin n) (R:=R))
    (Moments.projectSupport (V:=Fin n) (R:=R)) (canonical u J)
    Moments.Stored.ops_correct data ss]
  unfold bucketDenotation
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hs := hd s (by simp)
    have ht := ih (fun q hq => hd q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,map_add,supportDenotation] at ht ⊢
    rw [hs,Moments.projectSupport_canonical,ht]

theorem bucketDenotation_finite_output {G : Type*} {X : G → Type*} {vars : Finset (Fin n)}
    (gs : List G) (xs : ∀ g,List (X g)) (input : G → HeadInput)
    (encode : ∀ g,X g → List Bool)
    (hxs : ∀ g,(input g).assignments=(xs g).map (encode g))
    (D : ∀ g,X g → Moments.Stored (R:=R) vars u J)
    (w : Finset (Fin n) → ∀ g,X g → R)
    (bucket : List Bool) (ss : List (Finset (Fin n)))
    (hm : ∀ s∈ss,∀ g∈gs,∀ x∈xs g,
      semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩ (encode g x)=
        Moments.ringScalar (w s g x)*(D g x).denote) :
    semanticReadout u J (bucketDenotation u J semantic ss ⟨bucket,gs.map input⟩)=
      PolynomialAlgorithm.denote (Moments.outputCoefficients u J
        (MomentsAlgorithm.run Moments.Stored.ops (Moments.finiteRecords gs xs D w) ss).1.data) := by
  rw [bucketDenotation_eq_run u J semantic bucket (gs.map input) ss
    (Moments.finiteRecords gs xs D w)
    (fun s hs => heads_eq_finiteRecords u J semantic gs xs input encode hxs D w bucket s (hm s hs)),
    Moments.outputCoefficients_denote]
  rfl

/-- Native bucket denotations are interpreted in free variables before the
moment identity. No raw representative of a head or support is selected. -/
theorem bucketDenotation_embedded {G : Type*} {X : G → Type*} {vars : Finset (Fin n)}
    [Fintype G] [DecidableEq G] [∀ g,Fintype (X g)] [∀ g,DecidableEq (X g)]
    (gs : List G) (xs : ∀ g,List (X g)) (input : G → HeadInput)
    (encode : ∀ g,X g → List Bool)
    (hxs : ∀ g,(input g).assignments=(xs g).map (encode g))
    (D : ∀ g,X g → Moments.Stored (R:=R) vars u J)
    (w : Finset (Fin n) → ∀ g,X g → R)
    (bucket : List Bool) {V : Type*} [DecidableEq V]
    (e : V ↪ Fin n) {freeVars : Finset V}
    (F : ∀ g,X g → Moments.Stored (R:=R) freeVars u J)
    (wf : Finset V → ∀ g,X g → R)
    (hD : ∀ g x,(D g x).denote=ResidualEmbedding.jet e (F g x).denote)
    (hw : ∀ s g x,w (s.map e) g x=wf s g x)
    (hgs : gs.Nodup) (hgc : gs.toFinset=Finset.univ)
    (hxn : ∀ g,(xs g).Nodup) (hxc : ∀ g,(xs g).toFinset=Finset.univ)
    (ss : List (Finset (Fin n))) (freeSupports : List (Finset V))
    (hs : ss.Nodup) (hf : freeSupports.Nodup)
    (hmem : ∀ s,s.map e∈ss ↔ s∈freeSupports)
    (hM : ∀ s : Finset V,s.card < J → s∈freeSupports)
    (hm : ∀ s∈ss,∀ g∈gs,∀ x∈xs g,
      semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩ (encode g x)=
        Moments.ringScalar (w s g x)*(D g x).denote)
    (xval : (∀ g,X g) → V → R)
    (hidem : ∀ x v,xval x v*xval x v=xval x v)
    (hweight : ∀ s x,Moments.jetConstant (Squarefree.weight (xval x) s)=
      ∏ g,Moments.jetConstant (wf s g (x g))) :
    semanticReadout u J (bucketDenotation u J semantic ss ⟨bucket,gs.map input⟩)=
      ∑ x : ∀ g,X g,Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g,(F g (x g)).denote))) := by
  rw [bucketDenotation_finite_output u J semantic gs xs input encode hxs D w bucket ss hm]
  rw [ResidualEmbedding.run_finite_output e gs hgs hgc xs hxn hxc F D hD wf w hw
    freeSupports hf ss hs hmem]
  exact Moments.run_finite_bucket gs hgs hgc xs hxn hxc F wf freeSupports hf hM xval hidem hweight

end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
