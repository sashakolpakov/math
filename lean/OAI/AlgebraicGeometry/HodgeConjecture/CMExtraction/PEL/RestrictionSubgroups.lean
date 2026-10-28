import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionFiber
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SubgroupPullbackCoherence

/-! # Restriction Subgroups -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionSubgroups.IsogenyQuotient

noncomputable section

/-! Pulling a subgroup through the restricted universal source and then
to a branch agrees with transport through the original source point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' T : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)
  (c : T ⟶ Q') (x : T ⟶ X) (hx : c ≫ s' = x)

theorem restriction_subgroup_at_lift (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup (U.pullback s).abelian) :
    ((((H.pullback r).comapHom
      (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom).pullback c).comapHom
        (A.pullbackFactor c s' x hx).abelian.hom) =
      (((H.pullback (c ≫ r)).comapHom
        (U.pullbackFactor (c ≫ r) s (x ≫ i)
          (RestrictionFiber.IsogenyQuotient.restricted_source_lift i r s s' hs c x hx)).abelian.hom).comapHom
            (RestrictionFiber.IsogenyQuotient.pointFamilyIso A U i e x).abelian.hom) := by
  rw [SubgroupPullbackCoherence.IsogenyQuotient.subgroup_pullback_comap]
  rw [← SubgroupPullbackCoherence.IsogenyQuotient.subgroup_pullback_comp c r (U.pullback s) H]
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext z
  change (((z ≫ (A.pullbackFactor c s' x hx).abelian.hom) ≫
    (Over.pullback c).map (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom) ≫
      ((U.pullback s).pullbackComp r c).abelian.hom) ∈ (H.pullback (c ≫ r)).atTest V ↔
    (z ≫ (RestrictionFiber.IsogenyQuotient.pointFamilyIso A U i e x).abelian.hom) ≫
      (U.pullbackFactor (c ≫ r) s (x ≫ i)
        (RestrictionFiber.IsogenyQuotient.restricted_source_lift i r s s' hs c x hx)).abelian.hom ∈
          (H.pullback (c ≫ r)).atTest V
  have he := congrArg (fun f => z ≫ f)
    (RestrictionFiber.IsogenyQuotient.restrictionFamilyIso_at_lift A U i e r s s' hs c x hx)
  change z ≫ (((A.pullbackFactor c s' x hx).abelian.hom ≫
    (Over.pullback c).map (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom) ≫
      ((U.pullback s).pullbackComp r c).abelian.hom) =
    z ≫ ((RestrictionFiber.IsogenyQuotient.pointFamilyIso A U i e x).abelian.hom ≫
      (U.pullbackFactor (c ≫ r) s (x ≫ i)
        (RestrictionFiber.IsogenyQuotient.restricted_source_lift i r s s' hs c x hx)).abelian.hom) at he
  exact iff_of_eq (congrArg (fun y => y ∈ (H.pullback (c ≫ r)).atTest V)
    ((congrArg (fun f => f ≫ ((U.pullback s).pullbackComp r c).abelian.hom)
      (Category.assoc z (A.pullbackFactor c s' x hx).abelian.hom
        ((Over.pullback c).map (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom))).trans
          ((Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm))))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionSubgroups.IsogenyQuotient
