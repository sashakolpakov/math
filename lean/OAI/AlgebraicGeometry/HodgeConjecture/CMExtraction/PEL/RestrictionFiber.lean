import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.FactorProjections
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IteratedPullbackDetection

/-! # Restriction Fiber -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionFiber.IsogenyQuotient

noncomputable section

section

/-! The family comparison on a restricted correspondence agrees with
the comparison at each source point, after the canonical pullback maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' T : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)
  (c : T ⟶ Q') (x : T ⟶ X) (hx : c ≫ s' = x)

def pointFamilyIso : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) (U.pullback (x ≫ i)) :=
  (e.pullback x).trans (U.pullbackComp i x)

include hs hx in
theorem restricted_source_lift : (c ≫ r) ≫ s = x ≫ i :=
  (Category.assoc _ _ _).trans ((congrArg (fun f => c ≫ f) hs).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ i) hx)))

def coverLiftFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) ((U.pullback s).pullback (c ≫ r)) :=
  ((A.pullbackFactor c s' x hx).trans
    ((PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).pullback c)).trans
      ((U.pullback s).pullbackComp r c)

def pointLiftFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) ((U.pullback s).pullback (c ≫ r)) :=
  (pointFamilyIso A U i e x).trans
    (U.pullbackFactor (c ≫ r) s (x ≫ i) (restricted_source_lift i r s s' hs c x hx))

theorem pointFamilyIso_projection :
    (pointFamilyIso A U i e x).abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom (x ≫ i) =
      pullback.fst A.abelian.scheme.hom x ≫ e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i := by
  change (((Over.pullback x).map e.abelian.hom).left ≫
    (U.pullbackComp i x).abelian.hom.left) ≫ _ = _
  have hp := congrArg (fun f => ((Over.pullback x).map e.abelian.hom).left ≫ f)
    (FactorProjections.IsogenyQuotient.pelComp_projection U x i)
  have hn := congrArg (fun f => f ≫ pullback.fst U.abelian.scheme.hom i)
    (FactorProjections.IsogenyQuotient.pulled_morphism_projection e.abelian.hom x)
  exact (Category.assoc _ _ _).trans (hp.trans
    ((Category.assoc _ _ _).symm.trans (hn.trans (Category.assoc _ _ _))))

end

/-! Both routes from a retained source fiber to the original universal
isogeny's source give the same actual group morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem append_composite {C : Type*} [Category* C] {V W X Y Z : C}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) (k : V ⟶ Y)
    (he : f ≫ g ≫ h = k) (a : Y ⟶ Z) : f ≫ g ≫ h ≫ a = k ≫ a := by
  simpa only [Category.assoc] using congrArg (fun d => d ≫ a) he

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' T : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)
  (c : T ⟶ Q') (x : T ⟶ X) (hx : c ≫ s' = x)

theorem coverLiftFamilyIso_projection :
    (coverLiftFamilyIso A U i e r s s' hs c x hx).abelian.hom.left ≫
      pullback.fst (U.pullback s).abelian.scheme.hom (c ≫ r) ≫ pullback.fst U.abelian.scheme.hom s =
      pullback.fst A.abelian.scheme.hom x ≫ e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i := by
  let a := PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs
  let b := A.pullbackFactor c s' x hx
  let d := (U.pullback s).pullbackComp r c
  have hd : d.abelian.hom.left ≫
      pullback.fst (U.pullback s).abelian.scheme.hom (c ≫ r) ≫ pullback.fst U.abelian.scheme.hom s =
      pullback.fst ((U.pullback s).pullback r).abelian.scheme.hom c ≫
        pullback.fst (U.pullback s).abelian.scheme.hom r ≫ pullback.fst U.abelian.scheme.hom s := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ pullback.fst U.abelian.scheme.hom s)
        (FactorProjections.IsogenyQuotient.pelComp_projection (U.pullback s) c r)).trans (Category.assoc _ _ _))
  have hm : ((Over.pullback c).map a.abelian.hom).left ≫
      pullback.fst ((U.pullback s).pullback r).abelian.scheme.hom c ≫
        pullback.fst (U.pullback s).abelian.scheme.hom r ≫ pullback.fst U.abelian.scheme.hom s =
      pullback.fst (A.pullback s').abelian.scheme.hom c ≫ a.abelian.hom.left ≫
        pullback.fst (U.pullback s).abelian.scheme.hom r ≫ pullback.fst U.abelian.scheme.hom s := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ pullback.fst (U.pullback s).abelian.scheme.hom r ≫
        pullback.fst U.abelian.scheme.hom s) (FactorProjections.IsogenyQuotient.pulled_morphism_projection a.abelian.hom c)).trans
          (Category.assoc _ _ _))
  have ha : a.abelian.hom.left ≫ pullback.fst (U.pullback s).abelian.scheme.hom r ≫
      pullback.fst U.abelian.scheme.hom s =
      pullback.fst A.abelian.scheme.hom s' ≫ e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i :=
    RestrictionProjection.IsogenyQuotient.restrictionFamilyIso_projection A U i e r s s' hs
  change ((b.abelian.hom.left ≫ ((Over.pullback c).map a.abelian.hom).left) ≫ d.abelian.hom.left) ≫
    pullback.fst (U.pullback s).abelian.scheme.hom (c ≫ r) ≫ pullback.fst U.abelian.scheme.hom s = _
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (fun f => b.abelian.hom.left ≫ ((Over.pullback c).map a.abelian.hom).left ≫ f) hd).trans
      ((congrArg (fun f => b.abelian.hom.left ≫ f) hm).trans
        ((congrArg (fun f => b.abelian.hom.left ≫ pullback.fst (A.pullback s').abelian.scheme.hom c ≫ f) ha).trans
          (append_composite _ _ _ _ (FactorProjections.IsogenyQuotient.pelFactor_projection A c s' x hx)
            (e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i))))))

theorem pointLiftFamilyIso_projection :
    (pointLiftFamilyIso A U i e r s s' hs c x hx).abelian.hom.left ≫
      pullback.fst (U.pullback s).abelian.scheme.hom (c ≫ r) ≫ pullback.fst U.abelian.scheme.hom s =
      pullback.fst A.abelian.scheme.hom x ≫ e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i := by
  change ((pointFamilyIso A U i e x).abelian.hom.left ≫
    (U.pullbackFactor (c ≫ r) s (x ≫ i) (restricted_source_lift i r s s' hs c x hx)).abelian.hom.left) ≫
      pullback.fst (U.pullback s).abelian.scheme.hom (c ≫ r) ≫ pullback.fst U.abelian.scheme.hom s = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun f =>
    (pointFamilyIso A U i e x).abelian.hom.left ≫ f)
      (FactorProjections.IsogenyQuotient.pelFactor_projection U (c ≫ r) s (x ≫ i) (restricted_source_lift i r s s' hs c x hx))).trans
        (pointFamilyIso_projection A U i e x))

theorem restrictionFamilyIso_at_lift :
    (coverLiftFamilyIso A U i e r s s' hs c x hx).abelian.hom =
      (pointLiftFamilyIso A U i e r s s' hs c x hx).abelian.hom := by
  apply IteratedPullbackDetection.IsogenyQuotient.iterated_pullback_hom_ext U.abelian s (c ≫ r)
  exact (coverLiftFamilyIso_projection A U i e r s s' hs c x hx).trans
    (pointLiftFamilyIso_projection A U i e r s s' hs c x hx).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionFiber.IsogenyQuotient
