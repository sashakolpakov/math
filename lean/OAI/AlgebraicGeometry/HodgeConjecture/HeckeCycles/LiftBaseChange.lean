import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LiftBaseChange

/-! # Lift Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftBaseChange.CM

noncomputable section

/-! Base change of the actual smooth-point lift preserves its prescribed
geometric reduction, including after a finite evaluation extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {S : Scheme} {X : Over S}
  {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  {k : Type} [Field k] {e : k ≃+* IsLocalRing.ResidueField R}
  {bR : Spec (.of R) ⟶ S} {bk : Spec (.of k) ⟶ S}
  {p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X R e bR bk p)
  (f : R →+* R') (ρ : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField R')
  (hρ : ∀ r : R, ρ (IsLocalRing.residue R r) = IsLocalRing.residue R' (f r))

def baseChange : LiftMap.CM.SmoothPoint.IntegralLift X R' (e.trans ρ) (Spec.map (CommRingCat.ofHom f) ≫ bR) bk p where
  map := Spec.map (CommRingCat.ofHom f) ≫ l.map
  overBase := by rw [Category.assoc, l.overBase]
  reduction := by
    have hc : LiftMap.CM.SmoothPoint.closedBase R' ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ LiftMap.CM.SmoothPoint.closedBase R :=
      Isogenies.NeighborCounting.LiftBaseChange.Lifts.closedBase_baseChange f ρ hρ
    rw [← Category.assoc, hc, Category.assoc, l.reduction]
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ p.left ≫ pullback.fst X.hom bk =
      Spec.map (CommRingCat.ofHom (e.trans ρ).toRingHom) ≫ p.left ≫ pullback.fst X.hom bk
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

theorem baseChange_map : (baseChange l f ρ hρ).map = Spec.map (CommRingCat.ofHom f) ≫ l.map := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftBaseChange.CM
