import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange

/-! # Product Factor Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFactorBaseChange.CM

noncomputable section

/-! The actual coordinate inclusion of an Albanese factor commutes
with the canonical base-change comparison for its finite product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM

variable {S T : Scheme} {r : ℕ} (A : Fin r → CommGrp (Over S)) (b : T ⟶ S)

theorem factorMap_baseChange (i : Fin r) :
    (Over.pullback b).map (ProductPoints.CM.factorMap A i) ≫ (ProductBaseChange.CM.productBaseChangeIso A b).hom =
      ProductPoints.CM.factorMap (ProductBaseChange.CM.changedFactors A b) i := by
  apply AbelianScheme.TateComparison.Products.componentProduct_ext (ProductBaseChange.CM.changedFactors A b)
  intro j
  rw [Category.assoc, ProductBaseChange.CM.productBaseChangeIso_projection, ← Functor.map_comp]
  by_cases hij : i = j
  · subst j
    rw [ProductPoints.CM.factorMap_projection_self, ProductPoints.CM.factorMap_projection_self]
    exact (Over.pullback b).map_id (A i).X
  · rw [ProductPoints.CM.factorMap_projection_ne A i j hij, ProductPoints.CM.factorMap_projection_ne (ProductBaseChange.CM.changedFactors A b) i j hij]
    exact (Over.pullback b).map_one

theorem componentMap_baseChange {X : Over S} (i : Fin r) (a : X ⟶ (A i).X) :
    (Over.pullback b).map (a ≫ ProductPoints.CM.factorMap A i) ≫ (ProductBaseChange.CM.productBaseChangeIso A b).hom =
      (Over.pullback b).map a ≫ ProductPoints.CM.factorMap (ProductBaseChange.CM.changedFactors A b) i := by
  rw [Functor.map_comp, Category.assoc, factorMap_baseChange]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFactorBaseChange.CM
