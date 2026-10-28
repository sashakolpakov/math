import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Detection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components

/-! # Fiber Generation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

noncomputable section

/-! IntegralModel's finite-word generation transfers to the actual geometric
fiber, using the pullback adjunction and the genuine group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {S : Scheme} {k : Type} [Field k]

def mappedPointIso (b : Spec (.of k) ⟶ S) :
    (Over.map b).obj (Geometric.PointExt.CM.pointBase k) ≅ Over.mk b :=
  Over.isoMk (Iso.refl _) (by simp [Geometric.PointExt.CM.pointBase])

def testPointEquiv {T U X : Over S} (e : T ≅ U) : (T ⟶ X) ≃ (U ⟶ X) where
  toFun p := e.inv ≫ p
  invFun p := e.hom ≫ p
  left_inv p := by simp
  right_inv p := by simp

def testPointMulEquiv {T U G : Over S} [GrpObj G] (e : T ≅ U) :
    (T ⟶ G) ≃* (U ⟶ G) where
  toEquiv := testPointEquiv e
  map_mul' p q := MonObj.comp_mul e.inv p q

def fiberPointsEquiv (X : Over S) (b : Spec (.of k) ⟶ S) :
    (Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback b).obj X) ≃ (Over.mk b ⟶ X) :=
  (((Over.mapPullbackAdj b).homEquiv (Geometric.PointExt.CM.pointBase k) X).symm).trans
    (testPointEquiv (mappedPointIso b))

theorem fiberPointsEquiv_map {X Y : Over S} (a : X ⟶ Y)
    (b : Spec (.of k) ⟶ S) (x : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback b).obj X) :
    fiberPointsEquiv Y b (x ≫ (Over.pullback b).map a) =
      fiberPointsEquiv X b x ≫ a := by
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ ((x.left ≫ ((Over.pullback b).map a).left) ≫
    CategoryTheory.Limits.pullback.fst Y.hom b)) =
      (𝟙 _ ≫ (x.left ≫ CategoryTheory.Limits.pullback.fst X.hom b)) ≫ a.left
  simp only [Category.id_comp, Category.assoc, Over.pullback_map_left,
    CategoryTheory.Limits.pullback.lift_fst]

def fiberPointsMulEquiv {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (b : Spec (.of k) ⟶ S) :
    (Geometric.PointExt.CM.pointBase k ⟶ (A.pullback b).scheme) ≃* (Over.mk b ⟶ A.scheme) :=
  (A.baseChangePointsMulEquiv b (Geometric.PointExt.CM.pointBase k)).trans
    (testPointMulEquiv (mappedPointIso b))

def abelianFiberMap {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {X : Over S} (a : X ⟶ A.scheme) (b : Spec (.of k) ⟶ S) :
    (Over.pullback b).obj X ⟶ (A.pullback b).scheme :=
  (Over.pullback b).map a

theorem generation_on_fiber {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (X : Over S) (a : X ⟶ A.scheme) (b : Spec (.of k) ⟶ S) (n : ℕ)
    (h : Function.Surjective (fun z : Fin n → (Over.mk b ⟶ X) × (Over.mk b ⟶ X) =>
      ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a)))) :
    Function.Surjective (fun z : Fin n →
      (Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback b).obj X) × (Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback b).obj X) =>
      ∑ i, (Additive.ofMul ((z i).1 ≫ abelianFiberMap A a b) -
        Additive.ofMul ((z i).2 ≫ abelianFiberMap A a b))) := by
  let e := (fiberPointsMulEquiv A b).toAdditive
  intro x
  obtain ⟨z, hz⟩ := h (e x)
  refine ⟨fun i => ((fiberPointsEquiv X b).symm (z i).1,
    (fiberPointsEquiv X b).symm (z i).2), ?_⟩
  apply e.injective
  dsimp only
  rw [map_sum]
  calc
    _ = ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sub]
      congr 1 <;> apply Additive.toMul.injective
      · exact (fiberPointsEquiv_map a b _).trans
          (congrArg (· ≫ a) ((fiberPointsEquiv X b).apply_symm_apply (z i).1))
      · exact (fiberPointsEquiv_map a b _).trans
          (congrArg (· ≫ a) ((fiberPointsEquiv X b).apply_symm_apply (z i).2))
    _ = e x := hz

theorem component_generation_on_fiber [PreconnectedSpace S]
    {T : Over S} {r : ℕ} (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T r)
    (j : Fin r) [Smooth (D.A j).X.hom] [IsProper (D.A j).X.hom]
    [GeometricallyConnected (D.A j).X.hom]
    (t : PELModuli.IntegralModel.Base.GeometricPoint S) (n : ℕ)
    (h : Function.Surjective (D.sumOfDifferences j n t)) :
    letI : GrpObj ((Over.pullback t.morphism).obj (D.A j).X) :=
      ((Over.pullback t.morphism).mapCommGrp.obj (D.A j)).grp
    letI : IsCommMonObj ((Over.pullback t.morphism).obj (D.A j).X) :=
      ((Over.pullback t.morphism).mapCommGrp.obj (D.A j)).comm
    Function.Surjective (fun z : Fin n →
      (Geometric.PointExt.CM.pointBase t.field ⟶ (Over.pullback t.morphism).obj (D.S j)) ×
      (Geometric.PointExt.CM.pointBase t.field ⟶ (Over.pullback t.morphism).obj (D.S j)) =>
      ∑ i, (Additive.ofMul ((z i).1 ≫ (Over.pullback t.morphism).map (D.a j)) -
        Additive.ofMul ((z i).2 ≫ (Over.pullback t.morphism).map (D.a j)))) := by
  let s : S := t.morphism (IsLocalRing.closedPoint t.field)
  let A := AbelianDimension.CM.abelianScheme (D.A j).X s
  exact generation_on_fiber A (D.S j) (D.a j) t.morphism n h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM
