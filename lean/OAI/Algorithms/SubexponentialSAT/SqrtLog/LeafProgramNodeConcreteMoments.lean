import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyRelSemanticsBuckets

namespace OAI.Algorithms

/-! A direct polynomial form of the finite head-moment theorem. Native raw
witnesses need not be replaced by arbitrarily chosen sparse representatives. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open MomentsAssembly MomentsAssembly.Relational _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {R : Type*} [CommRing R] {n : ℕ}

theorem bucket_readout_polynomial (u J : ℕ)
    (semantic : AssignmentContext → List Bool → Jet (Fin n) R)
    (ss : List (Finset (Fin n))) (bucket : List Bool) (hs : List HeadInput) :
    semanticReadout u J (bucketDenotation u J semantic ss ⟨bucket,hs⟩) =
      Truncation.trunc J (Moments.sumUCoeff u ((ss.map fun s=>Moments.jetCoeff ⟨s⟩
        ((hs.map (headValue semantic (encodeMask s) bucket)).prod)).sum)) := by
  have hp (s : Finset (Fin n)) (F : Jet (Fin n) R) :
      semanticReadout u J (Moments.projectSupport s (canonical u J F)) =
      Truncation.trunc J (Moments.sumUCoeff u (Moments.jetCoeff ⟨s⟩ F)) := by
    rw [Moments.projectSupport_canonical]
    change Truncation.trunc J (Moments.sumUCoeff u
      (Moments.jetCoeff ⟨∅⟩ (canonical u J (Moments.projectSupport s F)))) = _
    rw [Moments.readout_canonical,Moments.jetCoeff_projectSupport]
  induction ss with
  | nil => simp [bucketDenotation]
  | cons s ss ih =>
    simp only [bucketDenotation,List.map_cons,List.sum_cons,map_add] at ih ⊢
    rw [show supportDenotation u J semantic bucket hs s =
      Moments.projectSupport s (canonical u J ((hs.map (headValue semantic (encodeMask s) bucket)).prod)) from rfl,hp]
    rw [show Truncation.trunc J
      (Moments.sumUCoeff u (Moments.jetCoeff ⟨s⟩ ((hs.map (headValue semantic (encodeMask s) bucket)).prod)) +
      Moments.sumUCoeff u ((ss.map fun s=>Moments.jetCoeff ⟨s⟩ ((hs.map (headValue semantic (encodeMask s) bucket)).prod)).sum)) =
      Truncation.trunc J (Moments.sumUCoeff u (Moments.jetCoeff ⟨s⟩ ((hs.map (headValue semantic (encodeMask s) bucket)).prod))) +
      Truncation.trunc J (Moments.sumUCoeff u ((ss.map fun s=>Moments.jetCoeff ⟨s⟩ ((hs.map (headValue semantic (encodeMask s) bucket)).prod)).sum)) from map_add (Truncation.truncAddHom J) _ _]
    exact congrArg (_ + ·) ih

theorem finite_polynomial_moments {V G : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {X : G → Type*}
    [∀ g,Fintype (X g)] [∀ g,DecidableEq (X g)]
    (u J : ℕ) (ss : Finset (Finset V))
    (hM : ∀ s : Finset V,s.card < J → s∈ss)
    (F : ∀ g,X g → Jet V R) (hF : ∀ g x,Admissible (F g x))
    (w : Finset V → ∀ g,X g → R)
    (xval : (∀ g,X g) → V → R) (hidem : ∀ x v,xval x v*xval x v=xval x v)
    (hweight : ∀ s x,Moments.jetConstant (weight (xval x) s)=
      ∏ g,Moments.jetConstant (w s g (x g))) :
    Truncation.trunc J (Moments.sumUCoeff u
      (∑ s∈ss,Moments.jetCoeff ⟨s⟩ (∏ g,∑ x,Moments.ringScalar (w s g x)*F g x))) =
      ∑ x : ∀ g,X g,Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g,F g (x g)))) := by
  let M : Finset (Support V) := ss.image Support.mk
  have hMk : ∀ s : Support V,s.vars.card < J → s∈M := by
    intro s hs
    exact Finset.mem_image.mpr ⟨s.vars,hM s.vars hs,by cases s; rfl⟩
  have h := Moments.squarefree_head_moments_trunc u J M hMk F hF xval hidem
    (fun s g x=>Moments.jetConstant (w s.vars g x)) (fun s x=>hweight s.vars x)
  have hinj : Function.Injective (Support.mk : Finset V → Support V) := by
    intro a b h
    exact congrArg Support.vars h
  simpa [M,Moments.extractMoments,Moments.momentProduct,Moments.headMoment,
    Finset.sum_image,hinj.eq_iff,← Moments.ringScalar_constant] using h

theorem bucket_polynomial_embedded {V G : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {X : G → Type*}
    [∀ g,Fintype (X g)] [∀ g,DecidableEq (X g)]
    (u J : ℕ) (semantic : AssignmentContext → List Bool → Jet (Fin n) R)
    (ss : List (Finset (Fin n))) (hs : ss.Nodup) (bucket : List Bool) (heads : List HeadInput)
    (e : V ↪ Fin n) (fs : Finset (Finset V))
    (hmem : ∀ s,s.map e∈ss ↔ s∈fs) (hM : ∀ s : Finset V,s.card < J → s∈fs)
    (F : ∀ g,X g → Jet V R) (hF : ∀ g x,Admissible (F g x))
    (wa : Finset (Fin n) → ∀ g,X g → R) (w : Finset V → ∀ g,X g → R)
    (hw : ∀ s g x,wa (s.map e) g x=w s g x)
    (hp : ∀ s∈ss,(heads.map (headValue semantic (encodeMask s) bucket)).prod =
      ResidualEmbedding.jet e (∏ g,∑ x,Moments.ringScalar (wa s g x)*F g x))
    (xval : (∀ g,X g) → V → R) (hidem : ∀ x v,xval x v*xval x v=xval x v)
    (hweight : ∀ s x,Moments.jetConstant (weight (xval x) s)=
      ∏ g,Moments.jetConstant (w s g (x g))) :
    semanticReadout u J (bucketDenotation u J semantic ss ⟨bucket,heads⟩) =
      ∑ x : ∀ g,X g,Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g,F g (x g)))) := by
  rw [bucket_readout_polynomial,← List.sum_toFinset _ hs]
  have he : (∑ s∈ss.toFinset,Moments.jetCoeff ⟨s⟩
      ((heads.map (headValue semantic (encodeMask s) bucket)).prod)) =
      ∑ s∈fs,Moments.jetCoeff ⟨s⟩ (∏ g,∑ x,Moments.ringScalar (w s g x)*F g x) := by
    calc
      _ = ∑ s∈ss.toFinset,Moments.jetCoeff ⟨s⟩
          (ResidualEmbedding.jet e (∏ g,∑ x,Moments.ringScalar (wa s g x)*F g x)) := by
        apply Finset.sum_congr rfl
        intro s hs'
        rw [hp s (List.mem_toFinset.mp hs')]
      _ = _ := by
        rw [ResidualEmbedding.sum_jetCoeff e ss.toFinset fs
          (fun s=>by simpa only [List.mem_toFinset] using hmem s)]
        simp_rw [hw]
  rw [he]
  exact finite_polynomial_moments u J fs hM F hF w xval hidem hweight

theorem head_product_embedded {V G : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {X : G → Type*}
    [∀ g,Fintype (X g)] [∀ g,DecidableEq (X g)]
    (semantic : AssignmentContext → List Bool → Jet (Fin n) R)
    (gs : List G) (hgn : gs.Nodup) (hgc : gs.toFinset=Finset.univ)
    (xs : ∀ g,List (X g)) (hxn : ∀ g,(xs g).Nodup) (hxc : ∀ g,(xs g).toFinset=Finset.univ)
    (input : G → HeadInput) (encode : ∀ g,X g → List Bool)
    (hassign : ∀ g,(input g).assignments=(xs g).map (encode g))
    (e : V ↪ Fin n) (F : ∀ g,X g → Jet V R) (w : ∀ g,X g → R)
    (s : Finset (Fin n)) (bucket : List Bool)
    (hm : ∀ g x,semantic ⟨encodeMask s,(input g).mask,(input g).context,bucket⟩ (encode g x)=
      Moments.ringScalar (w g x)*ResidualEmbedding.jet e (F g x)) :
    ((gs.map input).map (headValue semantic (encodeMask s) bucket)).prod =
      ResidualEmbedding.jet e (∏ g,∑ x,Moments.ringScalar (w g x)*F g x) := by
  simp only [List.map_map,Function.comp_def]
  rw [← List.prod_toFinset (fun g=>headValue semantic (encodeMask s) bucket (input g)) hgn,hgc,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  unfold headValue
  rw [hassign]
  simp only [List.map_map,Function.comp_def,hm]
  rw [← List.sum_toFinset (fun x=>Moments.ringScalar (w g x)*ResidualEmbedding.jet e (F g x)) (hxn g),hxc,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul,ResidualEmbedding.jet_ringScalar]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
