import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Product Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProductCoordinates.Comparison

noncomputable section

/-! The canonical comparison with a preserved product commutes with every original projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) {ι : Type w} (F : ι → C) [HasProduct F]
  [HasProduct (fun i => G.obj (F i))] [PreservesLimit (Discrete.functor F) G]

theorem inverse_projection (i : ι) : (PreservesProduct.iso G F).inv ≫ G.map (Pi.π F i) =
    Pi.π (fun i => G.obj (F i)) i := by
  apply (cancel_epi (PreservesProduct.iso G F).hom).mp
  exact (Iso.hom_inv_id_assoc (PreservesProduct.iso G F) (G.map (Pi.π F i))).trans
    (piComparison_comp_π G F i).symm

variable (F' : ι → D) [HasProductsOfShape ι D] (e : ∀ i, F' i ≅ G.obj (F i))

theorem projection (i : ι) :
    ((Pi.mapIso e) ≪≫ (PreservesProduct.iso G F).symm).hom ≫ G.map (Pi.π F i) = Pi.π F' i ≫ (e i).hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => (Pi.mapIso e).hom ≫ a) (inverse_projection G F i)).trans (Pi.mapIso_hom_π e i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProductCoordinates.Comparison
