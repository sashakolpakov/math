import OAI.AlgebraicGeometry.SmoothMorphisms.DVRLifting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt

/-! # Lift Map -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

/-! DVRLifting lifts actual points after a compatible change of residue field.
The conclusion records both the arithmetic-base square and the exact
reduction of the lifted morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {S : Scheme} (X : Over S)
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {k : Type} [Field k] (e : k ≃+* IsLocalRing.ResidueField R)
  (bR : Spec (.of R) ⟶ S) (bk : Spec (.of k) ⟶ S)

def closedBase : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

def residuePoint (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X) :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ X.left :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ p.left ≫ pullback.fst X.hom bk

theorem residuePoint_square
    (hbase : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ bk = closedBase R ≫ bR)
    (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X) :
    residuePoint X R e bk p ≫ X.hom = closedBase R ≫ bR := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ p.left ≫
    pullback.fst X.hom bk) ≫ X.hom = _
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc p.left]
  have hp : p.left ≫ pullback.snd X.hom bk = 𝟙 _ := p.w
  rw [hp, Category.id_comp]
  exact hbase

structure IntegralLift (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X) where
  map : Spec (.of R) ⟶ X.left
  overBase : map ≫ X.hom = bR
  reduction : closedBase R ≫ map = residuePoint X R e bk p

theorem integralLift_exists [Smooth X.hom]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hbase : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ bk = closedBase R ≫ bR)
    (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X) :
    Nonempty (IntegralLift X R e bR bk p) := by
  let Y := (Over.pullback bR).obj X
  have : Smooth Y.hom := inferInstanceAs (Smooth (pullback.snd X.hom bR))
  let pR : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Y.left :=
    pullback.lift (residuePoint X R e bk p) (closedBase R)
      (residuePoint_square X R e bR bk hbase p)
  have hpR : pR ≫ Y.hom = closedBase R := pullback.lift_snd _ _ _
  obtain ⟨l, hl, hred⟩ := SmoothMorphisms.DVRLifting.lift_special_fiber_point R Y.left Y.hom pR hpR
  refine ⟨⟨l ≫ pullback.fst X.hom bR, ?_, ?_⟩⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (l ≫ Y.hom) ≫ bR = _
    rw [hl, Category.id_comp]
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst X.hom bR) hred).trans
        (pullback.lift_fst _ _ _))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM

/-! Map an actual integral point lift along a morphism of arithmetic
models. The generic map and the prescribed special point remain the
images of the original lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {S : Scheme} {X Y : Over S} (f : X ⟶ Y)
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {k : Type} [Field k] (e : k ≃+* IsLocalRing.ResidueField R)
  (bR : Spec (.of R) ⟶ S) (bk : Spec (.of k) ⟶ S)
  (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X)
  (l : SmoothPoint.IntegralLift X R e bR bk p)

theorem residuePoint_map :
    SmoothPoint.residuePoint Y R e bk (p ≫ (Over.pullback bk).map f) = SmoothPoint.residuePoint X R e bk p ≫ f.left := by
  have h : ((Over.pullback bk).map f).left ≫ pullback.fst Y.hom bk =
      pullback.fst X.hom bk ≫ f.left := pullback.lift_fst _ _ _
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (p.left ≫ ((Over.pullback bk).map f).left) ≫ pullback.fst Y.hom bk = _
  simpa only [SmoothPoint.residuePoint, Category.assoc] using congrArg
    (fun z => Spec.map (CommRingCat.ofHom e.toRingHom) ≫ p.left ≫ z) h

def pushforward : SmoothPoint.IntegralLift Y R e bR bk (p ≫ (Over.pullback bk).map f) where
  map := l.map ≫ f.left
  overBase := (Category.assoc _ _ _).trans ((congrArg (l.map ≫ ·) f.w).trans l.overBase)
  reduction := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ f.left) l.reduction).trans (residuePoint_map f e bk p).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM

end

end OAI
