import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Relation Restriction On -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelationRestrictionOn.Construction.RelationRestriction

/-!
# Restriction of an equivalence relation to an invariant open

The restricted relation is constructed directly from the original reflexivity,
inverse and composition maps. This construction does not assume that a global
quotient already exists.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Restrict an internal equivalence relation along a monomorphism, when the
source restriction is cartesian and the target lands in the same subobject. -/
noncomputable def equivalenceRelation
    {C : Type u} [Category.{v} C] {R X R' X' : C}
    {s t : R ⟶ X} (e : CategoryTheory.EquivalenceRelation s t)
    (i : X' ⟶ X) [Mono i] (j : R' ⟶ R) (s' t' : R' ⟶ X')
    (hs : IsPullback s' j i s) (ht : t' ≫ i = j ≫ t)
    [HasPullback t' s'] : CategoryTheory.EquivalenceRelation s' t' := by
  have hr : 𝟙 X' ≫ i = (i ≫ e.r) ≫ s := by simp [e.reflexivity₁]
  have hinv : t' ≫ i = (j ≫ e.s) ≫ s := by simp [e.symmetry₁, ht]
  have hcomp : (pullback.fst t' s' ≫ j) ≫ t = (pullback.snd t' s' ≫ j) ≫ s := by
    rw [Category.assoc, ← ht, ← Category.assoc, pullback.condition,
      Category.assoc, hs.w, ← Category.assoc]
  let cm := PullbackCone.IsLimit.lift e.isLimit
    (pullback.fst t' s' ≫ j) (pullback.snd t' s' ≫ j) hcomp
  have hcm : (pullback.fst t' s' ≫ s') ≫ i = (cm ≫ e.t) ≫ s := by
    simpa only [cm, Category.assoc, e.transitivity₁, PullbackCone.IsLimit.lift_fst_assoc] using
      congrArg (fun k => pullback.fst t' s' ≫ k) hs.w
  let r' := hs.lift (𝟙 X') (i ≫ e.r) hr
  let inv' := hs.lift t' (j ≫ e.s) hinv
  let comp' := hs.lift (pullback.fst t' s' ≫ s') (cm ≫ e.t) hcm
  refine
    { r := r'
      s := inv'
      c := pullback.cone t' s'
      isLimit := pullback.isLimit t' s'
      t := comp'
      right_cancellation := ?_
      reflexivity₁ := ?_
      reflexivity₂ := ?_
      symmetry₁ := ?_
      symmetry₂ := ?_
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · intro T a b h₁ h₂
    apply hs.hom_ext h₁
    apply e.right_cancellation
    · simpa only [Category.assoc, ← hs.w] using congrArg (fun k => k ≫ i) h₁
    · simpa only [Category.assoc, ← ht] using congrArg (fun k => k ≫ i) h₂
  · exact hs.lift_fst _ _ _
  · apply (cancel_mono i).mp
    simp [r', Category.assoc, ht, e.reflexivity₂]
  · exact hs.lift_fst _ _ _
  · apply (cancel_mono i).mp
    simp [inv', Category.assoc, ht, e.symmetry₂, ← hs.w]
  · exact hs.lift_fst _ _ _
  · apply (cancel_mono i).mp
    simp only [Category.assoc, ht, comp', hs.lift_snd_assoc, e.transitivity₂]
    rw [← Category.assoc, PullbackCone.IsLimit.lift_snd]
    exact Category.assoc _ _ _

/-- An invariant open of a scheme with an internal equivalence relation
inherits that equivalence relation. -/
noncomputable def onOpen
    {R X : AlgebraicGeometry.Scheme.{u}} {s t : R ⟶ X}
    (e : CategoryTheory.EquivalenceRelation s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    CategoryTheory.EquivalenceRelation (AlgebraicGeometry.morphismRestrict s W)
      ((R.isoOfEq hW).hom ≫ AlgebraicGeometry.morphismRestrict t W) :=
  equivalenceRelation e W.ι (s ⁻¹ᵁ W).ι _ _
    (AlgebraicGeometry.isPullback_morphismRestrict s W) (by simp)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelationRestrictionOn.Construction.RelationRestriction
