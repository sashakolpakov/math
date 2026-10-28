import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionOverlapLifts

/-! # Cover Intersections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverIntersections

noncomputable section

/-! Closed subschemes compatible on the overlaps of ambient open pieces
have open pairwise intersections in the ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {J : Type u} (V Z : J → Scheme.{u})
variable (u : ∀ i, V i ⟶ X) (c : ∀ i, Z i ⟶ V i)
variable [∀ i, IsOpenImmersion (u i)] [∀ i, IsClosedImmersion (c i)]
variable (hc : ∀ i j, (c i).ker.comap (pullback.fst (u i) (u j)) =
  (c j).ker.comap (pullback.snd (u i) (u j)))

abbrev closedCoverMap (i : J) : Z i ⟶ X := c i ≫ u i

def closedCoverIntersectionLift (i j : J) : pullback (closedCoverMap V Z u c i) (u j) ⟶ Z j :=
  Classical.choose (ImmersionOverlapLifts.closedImmersion_overlap_lift (u i) (u j) (c i) (c j) (hc i j)
    (pullback.fst (closedCoverMap V Z u c i) (u j))
    (pullback.snd (closedCoverMap V Z u c i) (u j))
    (pullback.condition (f := closedCoverMap V Z u c i) (g := u j)))

omit [∀ i, IsOpenImmersion (u i)] in
@[reassoc]
theorem closedCoverIntersectionLift_fac (i j : J) :
    closedCoverIntersectionLift V Z u c hc i j ≫ c j =
      pullback.snd (closedCoverMap V Z u c i) (u j) :=
  Classical.choose_spec (ImmersionOverlapLifts.closedImmersion_overlap_lift (u i) (u j) (c i) (c j) (hc i j)
    (pullback.fst (closedCoverMap V Z u c i) (u j))
    (pullback.snd (closedCoverMap V Z u c i) (u j))
    (pullback.condition (f := closedCoverMap V Z u c i) (g := u j)))

theorem closedCoverIntersection_isPullback (i j : J) :
    IsPullback (pullback.fst (closedCoverMap V Z u c i) (u j))
      (closedCoverIntersectionLift V Z u c hc i j) (closedCoverMap V Z u c i) (closedCoverMap V Z u c j) := by
  apply IsPullback.mk'
  · exact pullback.condition.trans (closedCoverIntersectionLift_fac_assoc V Z u c hc i j (u j)).symm
  · intro W f g h _
    exact (cancel_mono (pullback.fst (closedCoverMap V Z u c i) (u j))).mp h
  · intro W a b h
    let l : W ⟶ pullback (closedCoverMap V Z u c i) (u j) :=
      pullback.lift a (b ≫ c j) ((h.trans (Category.assoc _ _ _).symm))
    refine ⟨l, pullback.lift_fst _ _ _, ?_⟩
    apply (cancel_mono (c j)).mp
    rw [Category.assoc, closedCoverIntersectionLift_fac]
    exact pullback.lift_snd _ _ _

include hc in
theorem closedCoverIntersection_fst_isOpenImmersion (i j : J) :
    IsOpenImmersion (pullback.fst (closedCoverMap V Z u c i) (closedCoverMap V Z u c j)) := by
  let h := closedCoverIntersection_isPullback V Z u c hc i j
  have H : IsOpenImmersion (h.isoPullback.inv ≫ pullback.fst (closedCoverMap V Z u c i) (u j)) :=
    inferInstance
  rwa [h.isoPullback_inv_fst] at H

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverIntersections
