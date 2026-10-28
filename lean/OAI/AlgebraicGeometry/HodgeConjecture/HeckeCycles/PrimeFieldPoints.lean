import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration

/-! # Prime Field Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints.CM

noncomputable section

/-! Coherent point equivalence for a geometric base factoring through
the prime-field fiber. Naturality retains the actual component maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

variable {S T : Scheme} {k : Type} [Field k]
  (b : T ⟶ S) (c : Spec (.of k) ⟶ T) (d : Spec (.of k) ⟶ S) (hd : c ≫ b = d)

def testIso : (Over.map b).obj (Over.mk c) ≅ Over.mk d :=
  Over.isoMk (Iso.refl _) (by change (𝟙 _) ≫ d = c ≫ b; exact (Category.id_comp _).trans hd.symm)

def primePointsToIntegral (X : Over S) :
    (Over.mk c ⟶ (Over.pullback b).obj X) ≃ (Over.mk d ⟶ X) :=
  (((Over.mapPullbackAdj b).homEquiv (Over.mk c) X).symm).trans
    (FiberGeneration.CM.testPointEquiv (testIso b c d hd))

def pointEquiv (X : Over S) :
    (Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback d).obj X) ≃
      (Over.mk c ⟶ (Over.pullback b).obj X) :=
  (FiberGeneration.CM.fiberPointsEquiv X d).trans (primePointsToIntegral b c d hd X).symm

theorem pointEquiv_projection (X : Over S)
    (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback d).obj X) :
    (pointEquiv b c d hd X p).left ≫ CategoryTheory.Limits.pullback.fst X.hom b =
      p.left ≫ CategoryTheory.Limits.pullback.fst X.hom d := by
  have h := congrArg (fun z : Over.mk d ⟶ X => z.left)
    ((primePointsToIntegral b c d hd X).apply_symm_apply (FiberGeneration.CM.fiberPointsEquiv X d p))
  change (𝟙 _ ≫ ((pointEquiv b c d hd X p).left ≫
      CategoryTheory.Limits.pullback.fst X.hom b)) =
    (𝟙 _ ≫ (p.left ≫ CategoryTheory.Limits.pullback.fst X.hom d)) at h
  simpa only [Category.id_comp] using h

theorem primePointsToIntegral_map {X Y : Over S} (a : X ⟶ Y)
    (p : Over.mk c ⟶ (Over.pullback b).obj X) :
    primePointsToIntegral b c d hd Y (p ≫ (Over.pullback b).map a) =
      primePointsToIntegral b c d hd X p ≫ a := by
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ ((p.left ≫ ((Over.pullback b).map a).left) ≫
      CategoryTheory.Limits.pullback.fst Y.hom b)) =
    (𝟙 _ ≫ (p.left ≫ CategoryTheory.Limits.pullback.fst X.hom b)) ≫ a.left
  simp only [Category.id_comp, Category.assoc, Over.pullback_map_left,
    CategoryTheory.Limits.pullback.lift_fst]

theorem pointEquiv_map {X Y : Over S} (a : X ⟶ Y)
    (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback d).obj X) :
    pointEquiv b c d hd Y (p ≫ (Over.pullback d).map a) =
      pointEquiv b c d hd X p ≫ (Over.pullback b).map a := by
  apply (primePointsToIntegral b c d hd Y).injective
  change primePointsToIntegral b c d hd Y
    ((primePointsToIntegral b c d hd Y).symm (FiberGeneration.CM.fiberPointsEquiv Y d
      (p ≫ (Over.pullback d).map a))) = _
  rw [Equiv.apply_symm_apply, FiberGeneration.CM.fiberPointsEquiv_map, primePointsToIntegral_map]
  exact congrArg (· ≫ a) ((primePointsToIntegral b c d hd X).apply_symm_apply
    (FiberGeneration.CM.fiberPointsEquiv X d p)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints.CM
