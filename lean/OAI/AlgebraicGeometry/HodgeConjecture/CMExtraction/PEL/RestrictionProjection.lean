import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection

/-! # Restriction Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionProjection.IsogenyQuotient

noncomputable section

/-! The transported family comparison retains the projection to the
original universal abelian scheme. This is the point-level identity used
when transporting the classified subgroup functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)

theorem restrictionFamilyIso_hom :
    (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom =
      (Over.pullback s').map e.abelian.hom ≫ (HeckeCycles.BaseChangeSquare.CM.squareIso s' r i s hs.symm U.abelian.scheme).hom := by
  change (Over.pullback s').map e.abelian.hom ≫
    ((U.abelian.pullbackCompIso i s').inv ≫ (U.pullbackFactor r s (s' ≫ i) hs).abelian.hom) = _
  rw [U.pullbackFactor_abelian, HeckeCycles.BaseChangeSquare.CM.groupFactor_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  rfl

theorem restrictionFamilyIso_projection :
    (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom.left ≫
      pullback.fst (pullback.snd U.abelian.scheme.hom s) r ≫ pullback.fst U.abelian.scheme.hom s =
      pullback.fst A.abelian.scheme.hom s' ≫ e.abelian.hom.left ≫ pullback.fst U.abelian.scheme.hom i := by
  have hh := congrArg (fun f => f.left) (restrictionFamilyIso_hom A U i e r s s' hs)
  have hp := (congrArg (fun f => f ≫
      pullback.fst (pullback.snd U.abelian.scheme.hom s) r ≫ pullback.fst U.abelian.scheme.hom s) hh).trans
    ((Category.assoc _ _ _).trans (congrArg (fun f => ((Over.pullback s').map e.abelian.hom).left ≫ f)
      (HeckeCycles.Source.SquareProjection.CM.square_hom_projection U.abelian.scheme s' r i s hs.symm)))
  have hn : ((Over.pullback s').map e.abelian.hom).left ≫
      pullback.fst (U.pullback i).abelian.scheme.hom s' =
      pullback.fst A.abelian.scheme.hom s' ≫ e.abelian.hom.left :=
    pullback.lift_fst _ _ _
  exact hp.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst U.abelian.scheme.hom i) hn).trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionProjection.IsogenyQuotient
