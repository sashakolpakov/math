import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Product Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM

noncomputable section

/-! The canonical base change of the arithmetic Albanese product is
isomorphic, as a group scheme, to the product of its geometric factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

variable {S T : Scheme} {r : ℕ} (A : Fin r → CommGrp (Over S)) (b : T ⟶ S)

abbrev changedFactors (i : Fin r) : CommGrp (Over T) :=
  AbelianScheme.TateComparison.BaseChange.baseChangedGroup (A i).X b

def productBaseChangeIso :
    (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X ≅
      (AbelianScheme.TateComparison.Products.componentProduct (changedFactors A b)).X :=
  (Over.pullback b).mapIso (AbelianScheme.TateComparison.Products.componentProductComparison A) ≪≫
    PreservesProduct.iso (Over.pullback b) (fun i => (A i).X) ≪≫
      (AbelianScheme.TateComparison.Products.componentProductComparison (changedFactors A b)).symm

theorem productBaseChangeIso_projection (i : Fin r) :
    (productBaseChangeIso A b).hom ≫ AbelianScheme.TateComparison.Products.componentProductProjection (changedFactors A b) i =
      (Over.pullback b).map (AbelianScheme.TateComparison.Products.componentProductProjection A i) := by
  simp only [productBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, ProductPoints.CM.comparison_inv_projection]
  rw [PreservesProduct.iso_hom, piComparison_comp_π, ← Functor.map_comp,
    AbelianScheme.TateComparison.Products.componentProductComparison_projection]

theorem productBaseChangeIso_group :
    letI : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X :=
      (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).grp
    IsMonHom (productBaseChangeIso A b).hom := by
  let : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X :=
    (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).grp
  let : ∀ i, GrpObj (changedFactors A b i).X := fun i => (changedFactors A b i).grp
  constructor
  · apply AbelianScheme.TateComparison.Products.componentProduct_ext (changedFactors A b)
    intro i
    let p : (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X ⟶ (changedFactors A b i).X :=
      (Over.pullback b).map (AbelianScheme.TateComparison.Products.componentProductProjection A i)
    calc
      _ = η ≫ p := by rw [Category.assoc, productBaseChangeIso_projection]
      _ = η := IsMonHom.one_hom p
      _ = _ := (IsMonHom.one_hom (AbelianScheme.TateComparison.Products.componentProductProjection (changedFactors A b) i)).symm
  · apply AbelianScheme.TateComparison.Products.componentProduct_ext (changedFactors A b)
    intro i
    rw [Category.assoc, productBaseChangeIso_projection]
    rw [Category.assoc,
      IsMonHom.mul_hom (AbelianScheme.TateComparison.Products.componentProductProjection (changedFactors A b) i)]
    rw [tensorHom_comp_tensorHom_assoc, productBaseChangeIso_projection]
    let p : (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X ⟶ (changedFactors A b i).X :=
      (Over.pullback b).map (AbelianScheme.TateComparison.Products.componentProductProjection A i)
    exact IsMonHom.mul_hom p

def productBaseChangeGroupIso :
    (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).toGrp ≅
      (AbelianScheme.TateComparison.Products.componentProduct (changedFactors A b)).toGrp := by
  let : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).X :=
    (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct A).X b).grp
  let e := productBaseChangeIso A b
  let : IsMonHom e.hom := productBaseChangeIso_group A b
  exact {
    hom := Grp.ofHom e.hom
    inv := Grp.ofHom e.inv
    hom_inv_id := by apply Grp.hom_ext; exact e.hom_inv_id
    inv_hom_id := by apply Grp.hom_ext; exact e.inv_hom_id }

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM
