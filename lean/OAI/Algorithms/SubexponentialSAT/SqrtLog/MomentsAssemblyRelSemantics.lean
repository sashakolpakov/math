import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsBuckets

namespace OAI.Algorithms

/-! Denotations of execution-associated payloads. Every assignment occurrence
may choose its own raw witness; the relation fixes only its semantic value. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

 theorem FoldRel.preserves {A W : Type*} {step : A → W → A → Prop}
    (P : A → Prop) (hstep : ∀ a x b,step a x b → P a → P b)
    {xs : List W} {a b : A} (h : FoldRel step xs a b) (ha : P a) : P b := by
  induction h with
  | nil => exact ha
  | cons hab hbc ih => exact ih (hstep _ _ _ hab ha)

 theorem FoldRel.sum_denote {A W B : Type*} [AddCommMonoid B]
    {step : A → W → A → Prop} (P : A → Prop)
    (hpres : ∀ a x b,step a x b → P a → P b)
    (f : A → B) (value : W → B)
    (hstep : ∀ a x b,step a x b → P a → f b=value x+f a)
    {xs : List W} {a b : A} (h : FoldRel step xs a b) (ha : P a) :
    f b=(xs.map value).sum+f a := by
  induction h with
  | nil => simp
  | cons hab hbc ih =>
    rw [ih (hpres _ _ _ hab ha),hstep _ _ _ hab ha]
    simp only [List.map_cons,List.sum_cons,add_assoc]
    exact add_left_comm _ _ _

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

 theorem head_nodup {c : AssignmentContext} {xs : List (List Bool)} {seed out : Raw p t (n:=n) (d:=d)}
    (h : HeadRel p t M cache table relation c xs seed out) (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys out).Nodup := by
  apply FoldRel.preserves (fun a => (Sparse.keys a).Nodup) _ h hn
  intro a x b hs ha
  obtain ⟨value,_,rfl⟩ := hs
  exact weightedValue_nodup p t M cache table value.1 value.2 a ha

include htable hsemantic in
 theorem head_denote {c : AssignmentContext} {xs : List (List Bool)} {seed out : Raw p t (n:=n) (d:=d)}
    (h : HeadRel p t M cache table relation c xs seed out) (hn : (Sparse.keys seed).Nodup) :
    denote p t M cache scalar basis out=(xs.map (semantic c)).sum+
      denote p t M cache scalar basis seed := by
  apply FoldRel.sum_denote (fun a => (Sparse.keys a).Nodup) _
    (denote p t M cache scalar basis) (semantic c) _ h hn
  · intro a x b hs ha
    obtain ⟨value,_,rfl⟩ := hs
    exact weightedValue_nodup p t M cache table value.1 value.2 a ha
  · intro a x b hs ha
    obtain ⟨value,hv,rfl⟩ := hs
    rw [weightedValue_denote p t M cache scalar basis table htable _ _ _ ha]
    change contributionDenote p t M cache scalar basis value+_=_
    rw [hsemantic c x value hv]

noncomputable def headValue (support bucket : List Bool) (h : HeadInput) : Jet (Fin n) R :=
  (h.assignments.map (semantic ⟨support,h.mask,h.context,bucket⟩)).sum

 theorem headStep_nodup {support bucket : List Bool} {left out : Raw p t (n:=n) (d:=d)} {h : HeadInput}
    (hs : HeadStep p t M cache table u J relation support bucket left h out) :
    (Sparse.keys out).Nodup := by
  obtain ⟨sum,_,rfl⟩ := hs
  exact Product.run_nodup p t M cache table u J left sum [] (by simp [Sparse.keys])

include htable hsemantic in
 theorem headStep_denote {support bucket : List Bool} {left out : Raw p t (n:=n) (d:=d)} {h : HeadInput}
    (hs : HeadStep p t M cache table u J relation support bucket left h out) :
    denote p t M cache scalar basis out=canonical u J
      (denote p t M cache scalar basis left*headValue semantic support bucket h) := by
  obtain ⟨sum,hr,rfl⟩ := hs
  unfold denote
  rw [Product.run_denote p t M cache scalar basis table htable u J left sum [] (by simp [Sparse.keys])]
  change canonical u J (denote p t M cache scalar basis left*
    denote p t M cache scalar basis sum)+0=_
  rw [head_denote p t M cache scalar basis table htable relation semantic hsemantic hr
    (by simp [Sparse.keys])]
  simp only [denote_nil,add_zero,headValue]
  rfl

 theorem heads_nodup {support bucket : List Bool} {hs : List HeadInput} {left out : Raw p t (n:=n) (d:=d)}
    (h : HeadsRel p t M cache table u J relation support bucket hs left out)
    (hn : (Sparse.keys left).Nodup) : (Sparse.keys out).Nodup := by
  apply FoldRel.preserves (fun a => (Sparse.keys a).Nodup) _ h hn
  intro a x b hs _
  exact headStep_nodup p t M cache table u J relation hs

include htable hsemantic in
 theorem heads_denote {support bucket : List Bool} {hs : List HeadInput} {left out : Raw p t (n:=n) (d:=d)}
    (h : HeadsRel p t M cache table u J relation support bucket hs left out)
    (hl : canonical u J (denote p t M cache scalar basis left)=denote p t M cache scalar basis left) :
    denote p t M cache scalar basis out=canonical u J
      (denote p t M cache scalar basis left*(hs.map (headValue semantic support bucket)).prod) := by
  induction h with
  | nil => simpa using hl.symm
  | @cons x xs a b c hab hbc ih =>
    have hd := headStep_denote p t M cache scalar basis table htable u J relation semantic hsemantic hab
    rw [ih (by rw [hd,Moments.canonical_idempotent]),hd,Moments.canonical_mul_left]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
