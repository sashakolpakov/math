import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyRelSemanticsLoops

namespace OAI.Algorithms

/-! Finite moment extraction from relational native assembly. The variable
universe is reduced before the Boolean moment identity is invoked. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j,basis i*basis j =
    ∑ k,scalar (wordValue p t (table i j k))*basis k)
  (u J : ℕ)
  (relation : AssignmentContext → List Bool → Contribution n (baseWidth p t) d → Prop)
  (semantic : AssignmentContext → List Bool → Jet (Fin n) R)
  (hsemantic : ∀ c x value,relation c x value →
    contributionDenote p t M cache scalar basis value=semantic c x)

include htable hsemantic in
 theorem supports_eq_run {vars : Finset (Fin n)}
    {bucket : List Bool} {hs : List HeadInput} {one out : Raw p t (n:=n) (d:=d)}
    {ss : List (Finset (Fin n))}
    (h : SupportsRel p t M cache table u J relation bucket hs one ss [] out)
    (ho : denote p t M cache scalar basis one=canonical u J 1)
    (data : Finset (Fin n) → List (List (R × Moments.Stored (R:=R) vars u J)))
    (hd : ∀ s∈ss,(hs.map (headValue semantic (encodeMask s) bucket))=
      ((data s).map fun l => (l.map fun a => Moments.ringScalar a.1*a.2.denote).sum)) :
    denote p t M cache scalar basis out=
      Moments.Stored.denote (MomentsAlgorithm.run Moments.Stored.ops data ss).1 := by
  rw [supports_denote p t M cache scalar basis table htable u J relation semantic hsemantic h
    (by simp [Sparse.keys]) ho,denote_nil,add_zero,
    MomentsAlgorithm.run_canonical
      (Moments.Stored.ops (R:=R) (vars:=vars) (t:=u) (J:=J))
      Moments.Stored.denote (Moments.ringScalar (V:=Fin n) (R:=R))
      (Moments.projectSupport (V:=Fin n) (R:=R)) (canonical u J)
      Moments.Stored.ops_correct data ss]
  clear h
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hs := hd s (by simp)
    have ht := ih (fun q hq => hd q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,map_add,supportDenotation] at ht ⊢
    rw [hs,Moments.projectSupport_canonical,ht]

variable {G : Type*} {X : G → Type*} {vars : Finset (Fin n)}
  (gs : List G) (xs : ∀ g,List (X g)) (input : G → HeadInput)
  (encode : ∀ g,X g → List Bool)
  (hxs : ∀ g,(input g).assignments=(xs g).map (encode g))
  (D : ∀ g,X g → Moments.Stored (R:=R) vars u J)
  (w : Finset (Fin n) → ∀ g,X g → R)
  (bucket : List Bool)

include hxs in
 theorem heads_eq_finiteRecords (s : Finset (Fin n))
    (hm : ∀ g∈gs,∀ x∈xs g,semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩
      (encode g x)=Moments.ringScalar (w s g x)*(D g x).denote) :
    ((gs.map input).map (headValue semantic (encodeMask s) bucket))=
      ((Moments.finiteRecords gs xs D w s).map fun l =>
        (l.map fun a => Moments.ringScalar a.1*a.2.denote).sum) := by
  simp only [List.map_map,Moments.finiteRecords,Function.comp_def]
  apply List.map_congr_left
  intro g hg
  unfold headValue
  rw [hxs g,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hm g hg x hx

include htable hsemantic hxs in
 theorem supports_finite_output
    {one out : Raw p t (n:=n) (d:=d)} {ss : List (Finset (Fin n))}
    (h : SupportsRel p t M cache table u J relation bucket (gs.map input) one ss [] out)
    (ho : denote p t M cache scalar basis one=canonical u J 1)
    (hm : ∀ s∈ss,∀ g∈gs,∀ x∈xs g,
      semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩ (encode g x)=
        Moments.ringScalar (w s g x)*(D g x).denote) :
    output p t M cache scalar basis u J out=
      PolynomialAlgorithm.denote (Moments.outputCoefficients u J
        (MomentsAlgorithm.run Moments.Stored.ops (Moments.finiteRecords gs xs D w) ss).1.data) := by
  rw [output_eq_semanticReadout,Moments.outputCoefficients_denote]
  have hh := supports_eq_run p t M cache scalar basis table htable u J relation semantic hsemantic
    h ho (Moments.finiteRecords gs xs D w)
    (fun s hs => heads_eq_finiteRecords u J semantic gs xs input encode hxs D w bucket s (hm s hs))
  rw [hh]
  rfl

include htable hsemantic hxs in
 theorem supports_embedded_finite_bucket {V : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] [∀ g,Fintype (X g)] [∀ g,DecidableEq (X g)]
    (e : V ↪ Fin n) {freeVars : Finset V}
    (F : ∀ g,X g → Moments.Stored (R:=R) freeVars u J)
    (wf : Finset V → ∀ g,X g → R)
    (hD : ∀ g x,(D g x).denote=ResidualEmbedding.jet e (F g x).denote)
    (hw : ∀ s g x,w (s.map e) g x=wf s g x)
    (hgs : gs.Nodup) (hgc : gs.toFinset=Finset.univ)
    (hxn : ∀ g,(xs g).Nodup) (hxc : ∀ g,(xs g).toFinset=Finset.univ)
    {one out : Raw p t (n:=n) (d:=d)} {ss : List (Finset (Fin n))}
    (h : SupportsRel p t M cache table u J relation bucket (gs.map input) one ss [] out)
    (freeSupports : List (Finset V)) (hs : ss.Nodup) (hf : freeSupports.Nodup)
    (hmem : ∀ s,s.map e∈ss ↔ s∈freeSupports)
    (hM : ∀ s : Finset V,s.card < J → s∈freeSupports)
    (ho : denote p t M cache scalar basis one=canonical u J 1)
    (hm : ∀ s∈ss,∀ g∈gs,∀ x∈xs g,
      semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩ (encode g x)=
        Moments.ringScalar (w s g x)*(D g x).denote)
    (xval : (∀ g,X g) → V → R)
    (hidem : ∀ x v,xval x v*xval x v=xval x v)
    (hweight : ∀ s x,Moments.jetConstant (Squarefree.weight (xval x) s)=
      ∏ g,Moments.jetConstant (wf s g (x g))) :
    output p t M cache scalar basis u J out=
      ∑ x : ∀ g,X g,Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g,(F g (x g)).denote))) := by
  rw [supports_finite_output p t M cache scalar basis table htable u J relation semantic hsemantic
    gs xs input encode hxs D w bucket h ho hm]
  rw [ResidualEmbedding.run_finite_output e gs hgs hgc xs hxn hxc F D hD wf w hw
    freeSupports hf ss hs hmem]
  exact Moments.run_finite_bucket gs hgs hgc xs hxn hxc F wf freeSupports hf hM xval hidem hweight

end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
