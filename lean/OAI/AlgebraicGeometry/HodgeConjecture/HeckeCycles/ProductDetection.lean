import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Detection

/-! # Product Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductDetection.CM

noncomputable section

/-! Ordinary differences on all components faithfully detect
endomorphisms of the actual total Albanese product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Detection.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM

variable {k : Type} [Field k] {r : ℕ}
  (A : Fin r → CommGrp (Over (Spec (.of k))))

def factorPointHom (j : Fin r) :
    Additive (Geometric.PointExt.CM.pointBase k ⟶ (A j).X) →+
      Additive (Geometric.PointExt.CM.pointBase k ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X) :=
  (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k)).symm.toAddMonoidHom.comp
    (AddMonoidHom.single (fun i => Additive (Geometric.PointExt.CM.pointBase k ⟶ (A i).X)) j)

theorem factorPointHom_point (j : Fin r) (p : Geometric.PointExt.CM.pointBase k ⟶ (A j).X) :
    factorPointHom A j (Additive.ofMul p) = Additive.ofMul (p ≫ ProductPoints.CM.factorMap A j) := by
  apply (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k)).injective
  exact ((ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k)).apply_symm_apply
    (Pi.single j (Additive.ofMul p))).trans (ProductPoints.CM.factorMap_on_points A _ j p).symm

theorem sum_factorPointHom (x : Additive (Geometric.PointExt.CM.pointBase k ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X)) :
    ∑ j, factorPointHom A j (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k) x j) = x := by
  classical
  apply (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k)).injective
  rw [map_sum]
  calc
    _ = ∑ j, Pi.single j (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k) x j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (ProductPoints.CM.productPointsAddEquiv A (Geometric.PointExt.CM.pointBase k)).apply_symm_apply _
    _ = _ := Finset.univ_sum_single _

variable [IsAlgClosed k]

theorem product_end_eq_zero_of_ordinary_differences
    (X : Fin r → Over (Spec (.of k)))
    [∀ j, IsReduced (X j).left] [∀ j, LocallyOfFiniteType (X j).hom]
    [IsReduced (AbelianScheme.TateComparison.Products.componentProduct A).X.left]
    [LocallyOfFiniteType (AbelianScheme.TateComparison.Products.componentProduct A).X.hom]
    [IsSeparated (AbelianScheme.TateComparison.Products.componentProduct A).X.hom]
    (a : ∀ j, X j ⟶ (A j).X)
    (U : ∀ j, (X j).left.Opens) (hU : ∀ j, Dense (U j : Set (X j).left))
    (n : Fin r → ℕ)
    (hgenerate : ∀ j, Function.Surjective (fun z : Fin (n j) →
      (Geometric.PointExt.CM.pointBase k ⟶ X j) × (Geometric.PointExt.CM.pointBase k ⟶ X j) =>
        ∑ i, (Additive.ofMul ((z i).1 ≫ a j) - Additive.ofMul ((z i).2 ≫ a j))))
    (f : AbelianScheme.TateComparison.End.IntegralEnd (AbelianScheme.TateComparison.Products.componentProduct A).X)
    (h : ∀ j (p q : Geometric.PointExt.CM.pointBase k ⟶ X j),
      p.left (IsLocalRing.closedPoint k) ∈ U j →
      q.left (IsLocalRing.closedPoint k) ∈ U j →
      PointEvaluationCM.CM.pointAction (AbelianScheme.TateComparison.Products.componentProduct A).X f
        (Additive.ofMul (p ≫ a j ≫ ProductPoints.CM.factorMap A j) -
          Additive.ofMul (q ≫ a j ≫ ProductPoints.CM.factorMap A j)) = 0) : f = 0 := by
  have hfactor : ∀ j x,
      PointEvaluationCM.CM.pointAction (AbelianScheme.TateComparison.Products.componentProduct A).X f (factorPointHom A j x) = 0 := by
    intro j x
    obtain ⟨z, rfl⟩ := hgenerate j x
    rw [map_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_sub, factorPointHom_point, factorPointHom_point]
    exact Ordinary.Detection.CM.kills_all_differences_of_ordinary (a j ≫ ProductPoints.CM.factorMap A j) (U j) (hU j)
      f (h j) (z i).1 (z i).2
  apply PointEvaluationCM.CM.end_eq_zero_of_points (AbelianScheme.TateComparison.Products.componentProduct A).X f
  intro x
  rw [← sum_factorPointHom A x, map_sum]
  exact Finset.sum_eq_zero (fun j _ => hfactor j _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductDetection.CM
