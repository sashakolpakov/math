import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyRelSemantics

namespace OAI.Algorithms

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

noncomputable def supportDenotation (bucket : List Bool) (hs : List HeadInput)
    (s : Finset (Fin n)) : Jet (Fin n) R :=
  Moments.projectSupport s (canonical u J
    ((hs.map (headValue semantic (encodeMask s) bucket)).prod))

 theorem supportStep_nodup {bucket : List Bool} {hs : List HeadInput} {one seed out : Raw p t (n:=n) (d:=d)}
    {s : Finset (Fin n)} (h : SupportStep p t M cache table u J relation bucket hs one seed s out)
    (hn : (Sparse.keys seed).Nodup) : (Sparse.keys out).Nodup := by
  obtain ⟨product,_,rfl⟩ := h
  exact supportValue_nodup p t M cache s product seed hn

include htable hsemantic in
 theorem supportStep_denote {bucket : List Bool} {hs : List HeadInput} {one seed out : Raw p t (n:=n) (d:=d)}
    {s : Finset (Fin n)} (h : SupportStep p t M cache table u J relation bucket hs one seed s out)
    (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one=canonical u J 1) :
    denote p t M cache scalar basis out=supportDenotation u J semantic bucket hs s+
      denote p t M cache scalar basis seed := by
  obtain ⟨product,hp,rfl⟩ := h
  rw [supportValue_denote p t M cache scalar basis s product seed hn]
  have hd := heads_denote p t M cache scalar basis table htable u J relation semantic hsemantic hp
    (by rw [ho,Moments.canonical_idempotent])
  rw [ho,Moments.canonical_mul_left,one_mul] at hd
  rw [hd]
  rfl

 theorem supports_nodup {bucket : List Bool} {hs : List HeadInput} {one seed out : Raw p t (n:=n) (d:=d)}
    {ss : List (Finset (Fin n))}
    (h : SupportsRel p t M cache table u J relation bucket hs one ss seed out)
    (hn : (Sparse.keys seed).Nodup) : (Sparse.keys out).Nodup := by
  apply FoldRel.preserves (fun a => (Sparse.keys a).Nodup) _ h hn
  intro a s b hs ha
  exact supportStep_nodup p t M cache table u J relation hs ha

include htable hsemantic in
 theorem supports_denote {bucket : List Bool} {hs : List HeadInput} {one seed out : Raw p t (n:=n) (d:=d)}
    {ss : List (Finset (Fin n))}
    (h : SupportsRel p t M cache table u J relation bucket hs one ss seed out)
    (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one=canonical u J 1) :
    denote p t M cache scalar basis out=(ss.map (supportDenotation u J semantic bucket hs)).sum+
      denote p t M cache scalar basis seed := by
  apply FoldRel.sum_denote (fun a => (Sparse.keys a).Nodup) _
    (denote p t M cache scalar basis) (supportDenotation u J semantic bucket hs) _ h hn
  · intro a s b hs ha
    exact supportStep_nodup p t M cache table u J relation hs ha
  · intro a s b hs ha
    exact supportStep_denote p t M cache scalar basis table htable u J relation semantic hsemantic hs ha ho

noncomputable def bucketDenotation (ss : List (Finset (Fin n))) (b : BucketInput) : Jet (Fin n) R :=
  (ss.map (supportDenotation u J semantic b.context b.heads)).sum

 theorem buckets_nodup {one seed out : Raw p t (n:=n) (d:=d)} {ss : List (Finset (Fin n))} {bs : List BucketInput}
    (h : BucketsRel p t M cache table u J relation ss one bs seed out)
    (hn : (Sparse.keys seed).Nodup) : (Sparse.keys out).Nodup := by
  apply FoldRel.preserves (fun a => (Sparse.keys a).Nodup) _ h hn
  intro a s b hs ha
  exact supports_nodup p t M cache table u J relation hs ha

include htable hsemantic in
 theorem buckets_denote {one seed out : Raw p t (n:=n) (d:=d)} {ss : List (Finset (Fin n))} {bs : List BucketInput}
    (h : BucketsRel p t M cache table u J relation ss one bs seed out)
    (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one=canonical u J 1) :
    denote p t M cache scalar basis out=(bs.map (bucketDenotation u J semantic ss)).sum+
      denote p t M cache scalar basis seed := by
  apply FoldRel.sum_denote (fun a => (Sparse.keys a).Nodup) _
    (denote p t M cache scalar basis) (bucketDenotation u J semantic ss) _ h hn
  · intro a s b hs ha
    exact supports_nodup p t M cache table u J relation hs ha
  · intro a s b hs ha
    exact supports_denote p t M cache scalar basis table htable u J relation semantic hsemantic hs ha ho

include htable hsemantic in
 theorem buckets_output {one seed out : Raw p t (n:=n) (d:=d)} {ss : List (Finset (Fin n))} {bs : List BucketInput}
    (h : BucketsRel p t M cache table u J relation ss one bs seed out)
    (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one=canonical u J 1) :
    output p t M cache scalar basis u J out=
      (bs.map (fun b => semanticReadout u J (bucketDenotation u J semantic ss b))).sum+
        output p t M cache scalar basis u J seed := by
  rw [output_eq_semanticReadout,
    buckets_denote p t M cache scalar basis table htable u J relation semantic hsemantic h hn ho,
    map_add,map_list_sum,output_eq_semanticReadout]
  simp only [List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
