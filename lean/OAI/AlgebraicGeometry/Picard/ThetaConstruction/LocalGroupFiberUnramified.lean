import OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedFiberStalk
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalOpenIdentity
import OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields

/-! # Local Group Fiber Unramified -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalGroupFiberUnramified.Geometric

noncomputable section

/-! An actual unramified closed field fiber makes a locally finite-type
group scheme over a local base formally unramified. The fiber supplies
the original identity stalk; no flatness or fiber-comparison hypothesis
is substituted for that stalk calculation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem unramified_stalk_of_mono_fieldFiber {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ S) [LocallyOfFiniteType f] (c : Spec (.of K) ⟶ S) [Mono c]
    [FormallyUnramified (pullback.snd f c)] (z : (pullback f c : Scheme.{u})) :
    (f.stalkMap (pullback.fst f c z)).hom.FormallyUnramified := by
  let x := pullback.fst f c z
  obtain ⟨w, hw⟩ := RepresentationTheory.Theta.Geometric.MonoResidueFields.residuePoint_hasLift (pullback.fst f c) (𝟙 X) x z rfl
  rw [Category.comp_id] at hw
  let b := w ≫ pullback.snd f c
  have hb : b ≫ c = X.fromSpecResidueField x ≫ f := by
    change (w ≫ pullback.snd f c) ≫ c = _
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hw]
  let e := pullbackLeftPullbackSndIso f c b
  have he : e.inv ≫ pullback.snd (pullback.snd f c) b = pullback.snd f (b ≫ c) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f c b]
    exact e.inv_hom_id_assoc _
  have hu : FormallyUnramified (e.inv ≫ pullback.snd (pullback.snd f c) b) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
        (IsPullback.of_hasPullback (pullback.snd f c) b) inferInstance)
  have hd : FormallyUnramified (pullback.snd f (b ≫ c)) := he ▸ hu
  rw [hb] at hd
  let := hd
  exact UnramifiedFiberStalk.Geometric.formallyUnramified_stalkMap_of_residueBaseChange f x

theorem localGroup_formallyUnramified_of_closedFieldFiber
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    (G : Over (Spec (.of R))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (c : Spec (.of K) ⟶ Spec (.of R)) [Mono c]
    (hc : c (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint R)
    [FormallyUnramified (pullback.snd G.hom c)] : FormallyUnramified G.hom := by
  have hunit : η[G].left ≫ G.hom = 𝟙 (Spec (.of R)) := η[G].w
  have hq : (c ≫ η[G].left) ≫ G.hom = (𝟙 (Spec (.of K))) ≫ c := by
    rw [Category.assoc, hunit, Category.comp_id, Category.id_comp]
  let q : Spec (.of K) ⟶ pullback G.hom c :=
    pullback.lift (c ≫ η[G].left) (𝟙 _) hq
  let z := q (IsLocalRing.closedPoint K)
  have hz : pullback.fst G.hom c z = η[G].left (IsLocalRing.closedPoint R) := by
    have h := congrArg (fun m : Spec (.of K) ⟶ G.left => m (IsLocalRing.closedPoint K))
      (pullback.lift_fst (c ≫ η[G].left) (𝟙 _) hq)
    change pullback.fst G.hom c z = η[G].left (c (IsLocalRing.closedPoint K)) at h
    exact h.trans (congrArg η[G].left hc)
  have h := unramified_stalk_of_mono_fieldFiber G.hom c z
  rw [hz] at h
  exact LocalOpenIdentity.Geometric.group_formallyUnramified_of_closed_identity_stalk G h

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalGroupFiberUnramified.Geometric
