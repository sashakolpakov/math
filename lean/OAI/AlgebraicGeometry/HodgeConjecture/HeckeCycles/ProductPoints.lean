import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products

/-! # Product Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM

noncomputable section

/-! The geometric points of the actual Albanese product are the product
of the component point groups. Coordinate inclusions are actual morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products

variable {S : Scheme} {r : ℕ} (A : Fin r → CommGrp (Over S))

theorem comparison_inv_projection (j : Fin r) :
    (AbelianScheme.TateComparison.Products.componentProductComparison A).inv ≫ AbelianScheme.TateComparison.Products.componentProductProjection A j =
      Pi.π (fun i => (A i).X) j := by
  rw [← AbelianScheme.TateComparison.Products.componentProductComparison_projection, Iso.inv_hom_id_assoc]

def productPointsEquiv (T : Over S) :
    (T ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X) ≃* (∀ j, T ⟶ (A j).X) where
  toFun p j := p ≫ AbelianScheme.TateComparison.Products.componentProductProjection A j
  invFun p := Pi.lift p ≫ (AbelianScheme.TateComparison.Products.componentProductComparison A).inv
  left_inv p := by
    apply AbelianScheme.TateComparison.Products.componentProduct_ext A
    intro j
    simp only [Category.assoc, comparison_inv_projection, Pi.lift_comp_π]
  right_inv p := by
    funext j
    simp only [Category.assoc, comparison_inv_projection, Pi.lift_comp_π]
  map_mul' p q := by
    funext j
    exact MonObj.mul_comp p q (AbelianScheme.TateComparison.Products.componentProductProjection A j)

def productPointsAddEquiv (T : Over S) :
    Additive (T ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X) ≃+
      (∀ j, Additive (T ⟶ (A j).X)) where
  toFun p j := Additive.ofMul (productPointsEquiv A T p.toMul j)
  invFun p := Additive.ofMul ((productPointsEquiv A T).symm (fun j => (p j).toMul))
  left_inv p := congrArg Additive.ofMul ((productPointsEquiv A T).symm_apply_apply p.toMul)
  right_inv p := by
    funext j
    exact congrArg (fun x => Additive.ofMul (x j))
      ((productPointsEquiv A T).apply_symm_apply (fun i => (p i).toMul))
  map_add' p q := by
    funext j
    exact congrArg (fun x => Additive.ofMul (x j))
      ((productPointsEquiv A T).map_mul p.toMul q.toMul)

def factorMap (j : Fin r) : (A j).X ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X :=
  Pi.lift (fun i => if h : j = i then eqToHom (congrArg (fun z => (A z).X) h) else 1) ≫
    (AbelianScheme.TateComparison.Products.componentProductComparison A).inv

theorem factorMap_projection_self (j : Fin r) :
    factorMap A j ≫ AbelianScheme.TateComparison.Products.componentProductProjection A j = 𝟙 _ := by
  simp [factorMap, comparison_inv_projection]

theorem factorMap_projection_ne (i j : Fin r) (h : i ≠ j) :
    factorMap A i ≫ AbelianScheme.TateComparison.Products.componentProductProjection A j = 1 := by
  simp [factorMap, comparison_inv_projection, h]

theorem factorMap_on_points (T : Over S) (j : Fin r) (p : T ⟶ (A j).X) :
    productPointsAddEquiv A T (Additive.ofMul (p ≫ factorMap A j)) =
      Pi.single j (Additive.ofMul p) := by
  classical
  funext i
  by_cases h : j = i
  · subst i
    change Additive.ofMul (p ≫ factorMap A j ≫ AbelianScheme.TateComparison.Products.componentProductProjection A j) = _
    rw [factorMap_projection_self, Category.comp_id, Pi.single_eq_same]
  · change Additive.ofMul (p ≫ factorMap A j ≫ AbelianScheme.TateComparison.Products.componentProductProjection A i) = _
    rw [factorMap_projection_ne A j i h, MonObj.comp_one, Pi.single_eq_of_ne (Ne.symm h)]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM
