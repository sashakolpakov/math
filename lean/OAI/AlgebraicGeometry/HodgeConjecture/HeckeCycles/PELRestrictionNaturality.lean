import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackHomExt

/-! # PEL Restriction Naturality -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM.Projection

/-! The PEL restriction comparison preserves the map to the original
universal abelian scheme on every branch of the correspondence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction.IsogenyQuotient

variable {S T V : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem factor_projection (f : V ⟶ T) (h : T ⟶ S) (x : V ⟶ S) (w : f ≫ h = x) :
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A f h x w).hom.left ≫
      pullback.fst (pullback.snd A.scheme.hom h) f ≫ pullback.fst A.scheme.hom h =
        pullback.fst A.scheme.hom x := by
  rw [BaseChangeSquare.CM.groupFactor_hom]
  exact Source.SquareProjection.CM.factor_hom_projection f h x w A.scheme

variable {R : Type} [CommRing R] {N : ℕ} {X Y Q Q' : Scheme}
  (F : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso F (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)

theorem scheme_projection (A₀ : Over X) (U₀ : Over Y)
    (e₀ : A₀ ⟶ (Over.pullback i).obj U₀) :
    (((Over.pullback s').map e₀).left ≫
      ((Over.pullbackComp s' i).app U₀).inv.left ≫
      (BaseChangeSquare.CM.factorIso r s (s' ≫ i) hs U₀).hom.left) ≫
        pullback.fst (pullback.snd U₀.hom s) r ≫ pullback.fst U₀.hom s =
      pullback.fst A₀.hom s' ≫ e₀.left ≫ pullback.fst U₀.hom i := by
  simp only [Category.assoc]
  rw [Source.SquareProjection.CM.factor_hom_projection]
  rw [Source.SquareProjection.CM.pullbackComp_inv_projection]
  rw [← Category.assoc]
  exact (congrArg (fun f => f ≫ pullback.fst U₀.hom i)
    (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst e₀ s')).trans (Category.assoc _ _ _)

theorem restriction_projection :
    (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso F U i e r s s' hs).abelian.hom.left ≫
      pullback.fst (pullback.snd U.abelian.scheme.hom s) r ≫ pullback.fst U.abelian.scheme.hom s =
        pullback.fst F.abelian.scheme.hom s' ≫ e.abelian.hom.left ≫
          pullback.fst U.abelian.scheme.hom i := by
  change (((Over.pullback s').map e.abelian.hom).left ≫
    (U.abelian.pullbackCompIso i s').inv.left ≫
    (U.pullbackFactor r s (s' ≫ i) hs).abelian.hom.left) ≫ _ ≫ _ = _
  rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullbackFactor_abelian]
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv, BaseChangeSquare.CM.groupFactor_hom]
  exact scheme_projection i r s s' hs F.abelian.scheme U.abelian.scheme e.abelian.hom

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM.Projection

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM.Scheme

/-! Restricting an original family and then following a correspondence
branch gives the same scheme map as following its original branch. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y Q Q' : Scheme.{0}} (A : Over X) (U : Over Y)
  (i : X ⟶ Y) (e : A ⟶ (Over.pullback i).obj U)
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)

def map : (Over.pullback s').obj A ⟶
    (Over.pullback r).obj ((Over.pullback s).obj U) :=
  (Over.pullback s').map e ≫ ((Over.pullbackComp s' i).app U).inv ≫
    (BaseChangeSquare.CM.factorIso r s (s' ≫ i) hs U).hom

theorem projection :
    (CM.Scheme.map A U i e r s s' hs).left ≫
      pullback.fst (pullback.snd U.hom s) r ≫ pullback.fst U.hom s =
        pullback.fst A.hom s' ≫ e.left ≫ pullback.fst U.hom i := by
  unfold CM.Scheme.map
  rw [Over.comp_left, Over.comp_left]
  have h := Projection.scheme_projection i r s s' hs A U e
  simp only [Category.assoc] at h ⊢
  exact h

theorem factor_projection {S T V : Scheme.{0}} (B : Over S)
    (f : V ⟶ T) (h : T ⟶ S) (x : V ⟶ S) (w : f ≫ h = x) :
    (BaseChangeSquare.CM.factorIso f h x w B).hom.left ≫
      pullback.fst (pullback.snd B.hom h) f ≫ pullback.fst B.hom h =
        pullback.fst B.hom x :=
  Source.SquareProjection.CM.factor_hom_projection f h x w B

theorem at_branch {Z : Scheme.{0}} (c : Z ⟶ Q') (x : Z ⟶ X) (wc : c ≫ s' = x)
    (hc : (c ≫ r) ≫ s = x ≫ i) :
    (BaseChangeSquare.CM.factorIso c s' x wc A).hom ≫
      (Over.pullback c).map (CM.Scheme.map A U i e r s s' hs) =
    CM.Scheme.map A U i e (c ≫ r) s x hc ≫
      (BaseChangeSquare.CM.factorIso c r (c ≫ r) rfl ((Over.pullback s).obj U)).hom := by
  apply PullbackHomExt.CM.thrice U s r c
  have h₀ := congrArg (fun z =>
    (BaseChangeSquare.CM.factorIso c s' x wc A).hom.left ≫ z ≫
      pullback.fst (pullback.snd U.hom s) r ≫ pullback.fst U.hom s)
    (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (CM.Scheme.map A U i e r s s' hs) c)
  have h₁ := congrArg (fun z =>
    (BaseChangeSquare.CM.factorIso c s' x wc A).hom.left ≫
      pullback.fst (pullback.snd A.hom s') c ≫ z)
    (projection A U i e r s s' hs)
  have h₂ := congrArg (fun z => z ≫ e.left ≫ pullback.fst U.hom i)
    (factor_projection A c s' x wc)
  have h₃ := congrArg (fun z => (CM.Scheme.map A U i e (c ≫ r) s x hc).left ≫ z ≫
    pullback.fst U.hom s)
    (factor_projection ((Over.pullback s).obj U) c r (c ≫ r) rfl)
  have h₄ := projection A U i e (c ≫ r) s x hc
  simp only [Over.comp_left, Category.assoc] at h₀ h₁ h₂ h₃ h₄ ⊢
  exact (h₀.trans (h₁.trans h₂)).trans (h₃.trans h₄).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM.Scheme

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM

/-! Canonical PEL-family comparisons commute with following a branch,
before passing to its kernel subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction.IsogenyQuotient

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)

def atPoint {Z : Scheme} (x : Z ⟶ X) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) (U.pullback (x ≫ i)) :=
  (e.pullback x).trans (U.pullbackComp i x)

theorem restriction_abelian :
    (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom =
      CM.Scheme.map A.abelian.scheme U.abelian.scheme i
        e.abelian.hom r s s' hs := by
  change (Over.pullback s').map e.abelian.hom ≫
    (U.abelian.pullbackCompIso i s').inv ≫
    (U.pullbackFactor r s (s' ≫ i) hs).abelian.hom = _
  rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullbackFactor_abelian, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv,
    BaseChangeSquare.CM.groupFactor_hom]
  rfl

theorem atPoint_abelian {Z : Scheme} (x : Z ⟶ X) :
    (atPoint A U i e x).abelian.hom =
      (Over.pullback x).map e.abelian.hom ≫
        ((Over.pullbackComp x i).app U.abelian.scheme).inv := by
  change (Over.pullback x).map e.abelian.hom ≫ (U.abelian.pullbackCompIso i x).inv = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  rfl

theorem at_branch {Z : Scheme} (c : Z ⟶ Q') (x : Z ⟶ X) (wc : c ≫ s' = x)
    (hc : (c ≫ r) ≫ s = x ≫ i) :
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A.abelian c s' x wc).hom ≫
      (Over.pullback c).map (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom =
    (atPoint A U i e x).abelian.hom ≫
      (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso U.abelian (c ≫ r) s (x ≫ i) hc).hom ≫
        (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso (U.abelian.pullback s) c r (c ≫ r) rfl).hom := by
  rw [restriction_abelian, atPoint_abelian,
    BaseChangeSquare.CM.groupFactor_hom, BaseChangeSquare.CM.groupFactor_hom,
    BaseChangeSquare.CM.groupFactor_hom]
  have h := CM.Scheme.at_branch A.abelian.scheme U.abelian.scheme i
    e.abelian.hom r s s' hs c x wc hc
  unfold CM.Scheme.map at h ⊢
  simp only [Category.assoc] at h ⊢
  exact h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality.CM

end

end OAI
