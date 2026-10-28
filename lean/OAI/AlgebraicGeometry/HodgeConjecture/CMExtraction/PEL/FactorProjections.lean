import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection

/-! # Factor Projections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.FactorProjections.IsogenyQuotient

noncomputable section

/-! Projection identities for the canonical PEL pullback comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {g N : ℕ} {S T V : Scheme}
  (F : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) (b : V ⟶ T) (s : T ⟶ S) (x : V ⟶ S) (hx : b ≫ s = x)

theorem pelFactor_projection :
    (F.pullbackFactor b s x hx).abelian.hom.left ≫
      pullback.fst (pullback.snd F.abelian.scheme.hom s) b ≫ pullback.fst F.abelian.scheme.hom s =
      pullback.fst F.abelian.scheme.hom x := by
  have he := (congrArg (fun e => e.hom.left) (F.pullbackFactor_abelian b s x hx)).trans
    (congrArg (fun f => f.left) (HeckeCycles.BaseChangeSquare.CM.groupFactor_hom b s x hx F.abelian))
  exact (congrArg (fun f => f ≫ pullback.fst (pullback.snd F.abelian.scheme.hom s) b ≫
    pullback.fst F.abelian.scheme.hom s) he).trans
    (HeckeCycles.Source.SquareProjection.CM.factor_hom_projection b s x hx F.abelian.scheme)

theorem pelComp_projection :
    (F.pullbackComp s b).abelian.hom.left ≫ pullback.fst F.abelian.scheme.hom (b ≫ s) =
      pullback.fst (pullback.snd F.abelian.scheme.hom s) b ≫ pullback.fst F.abelian.scheme.hom s := by
  change (F.abelian.pullbackCompIso s b).inv.left ≫ _ = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  exact HeckeCycles.Source.SquareProjection.CM.pullbackComp_inv_projection b s F.abelian.scheme

variable {X Y Z : Over S} (e : X ⟶ Y) (c : T ⟶ S)

theorem pulled_morphism_projection :
    ((Over.pullback c).map e).left ≫ pullback.fst Y.hom c = pullback.fst X.hom c ≫ e.left :=
  pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.FactorProjections.IsogenyQuotient
