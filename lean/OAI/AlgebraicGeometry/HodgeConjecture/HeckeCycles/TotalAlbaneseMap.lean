import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components

/-! # Total Albanese Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TotalAlbaneseMap.CM

noncomputable section

/-! The arithmetic total Albanese map restricts on each original
component to its component Albanese map followed by the actual factor
inclusion into the group product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM

variable {B : Scheme} {T : Over B} {r : ℕ}
  (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T r) (e : (∐ D.S) ≅ T)

def map : T ⟶ (AbelianScheme.TateComparison.Products.componentProduct D.A).X :=
  D.totalMap e ≫ (AbelianScheme.TateComparison.Products.componentProductComparison D.A).inv

theorem component (i : Fin r) :
    (Sigma.ι D.S i ≫ e.hom) ≫ map D e = D.a i ≫ ProductPoints.CM.factorMap D.A i := by
  apply AbelianScheme.TateComparison.Products.componentProduct_ext D.A
  intro j
  simp only [map, Category.assoc, ProductPoints.CM.comparison_inv_projection]
  rw [D.totalMap_coordinate]
  by_cases hij : i = j
  · subst j
    rw [D.coordinateMap_self, ProductPoints.CM.factorMap_projection_self, Category.comp_id]
  · rw [D.coordinateMap_ne i j hij, ProductPoints.CM.factorMap_projection_ne D.A i j hij, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TotalAlbaneseMap.CM
