import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup

/-! # Albanese Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseCoordinates

noncomputable section

/-! The full product Albanese point group is identified with all of its
component point groups, compatibly with the actual component maps. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace Construction
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup

theorem componentProductComparison_inv_projection {S : Scheme.{0}} {r : ℕ}
    (A : Fin r → CommGrp (Over S)) (j : Fin r) :
    (TateComparison.Products.componentProductComparison A).inv ≫ TateComparison.Products.componentProductProjection A j =
      Pi.π (fun k => (A k).X) j := by
  apply (cancel_epi (TateComparison.Products.componentProductComparison A).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (TateComparison.Products.componentProductComparison_projection A j).symm

def componentProductPointsEquiv {S : Scheme.{0}} {r : ℕ}
    (A : Fin r → CommGrp (Over S)) (T : Over S) :
    Additive (T ⟶ (TateComparison.Products.componentProduct A).X) ≃+
      ∀ j, Additive (T ⟶ (A j).X) where
  toFun x j := Additive.ofMul (x.toMul ≫ TateComparison.Products.componentProductProjection A j)
  invFun y := Additive.ofMul
    (Pi.lift (fun j => (y j).toMul) ≫ (TateComparison.Products.componentProductComparison A).inv)
  left_inv x := by
    apply Additive.toMul.injective
    apply TateComparison.Products.componentProduct_ext A
    intro j
    change (Pi.lift (fun j => x.toMul ≫ TateComparison.Products.componentProductProjection A j) ≫
      (TateComparison.Products.componentProductComparison A).inv) ≫ TateComparison.Products.componentProductProjection A j = _
    simp only [Category.assoc, componentProductComparison_inv_projection, Pi.lift_comp_π]
  right_inv y := by
    funext j
    apply Additive.toMul.injective
    change (Pi.lift (fun j => (y j).toMul) ≫ (TateComparison.Products.componentProductComparison A).inv) ≫
      TateComparison.Products.componentProductProjection A j = (y j).toMul
    simp only [Category.assoc, componentProductComparison_inv_projection, Pi.lift_comp_π]
  map_add' x y := by
    funext j
    apply Additive.toMul.injective
    exact MonObj.mul_comp x.toMul y.toMul (TateComparison.Products.componentProductProjection A j)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def albanesePointCoordinates (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (T : Over (Spec (.of K))) :
    Additive (T ⟶ D.albaneseGroup.X) ≃+
      ∀ j, Additive ((Over.map D.generic).obj T ⟶ (D.components.A j).X) :=
  (PELModuli.IntegralModel.Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv
    (TateComparison.Products.componentProduct D.components.A).X D.generic T).toAdditive.trans
      (componentProductPointsEquiv D.components.A ((Over.map D.generic).obj T))

theorem albanesePointCoordinates_aPoint
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (T : Over (Spec (.of K))) (j k : Fin D.componentCount)
    (x : T ⟶ D.componentGeneric j) :
    albanesePointCoordinates D T (D.aPoint hgeometry j x) k =
      Additive.ofMul (TateComparison.Subgroup.pullbackPointsEquiv (D.components.S j) D.generic T x ≫
        D.components.coordinateMap j k) := by
  have : IsIso D.componentAssembly := hgeometry.decomposition
  let e := asIso D.componentAssembly
  have hc : (TateComparison.Products.componentProductComparison D.components.A).inv ≫
      TateComparison.Products.componentProductProjection D.components.A k = Pi.π (fun l => (D.components.A l).X) k :=
    componentProductComparison_inv_projection D.components.A k
  have ht : D.inclusion j ≫ D.components.totalMap e ≫
      Pi.π (fun l => (D.components.A l).X) k = D.components.coordinateMap j k := by
    simpa only [e, asIso_hom, TateComparison.Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc_assoc]
      using D.components.totalMap_coordinate e j k
  apply Additive.toMul.injective
  change TateComparison.Subgroup.pullbackPointsEquiv (TateComparison.Products.componentProduct D.components.A).X D.generic T
      ((x ≫ (Over.pullback D.generic).map (D.inclusion j)) ≫
        (Over.pullback D.generic).map (D.components.totalMap e ≫
          (TateComparison.Products.componentProductComparison D.components.A).inv)) ≫
        TateComparison.Products.componentProductProjection D.components.A k = _
  rw [Category.assoc, ← Functor.map_comp, TateComparison.Subgroup.pullbackPointsEquiv_map]
  simp only [Category.assoc, hc]
  rw [ht]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseCoordinates
