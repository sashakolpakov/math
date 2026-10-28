import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Open Product Preservation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation.AffineOpenProductPreservation

noncomputable section

/-! Inclusion of affine opens preserves every finite nonempty tuple product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable (X : Scheme.{u}) [X.IsSeparated]

theorem product_iInf {C : Type u} [CompleteLattice C] {ι : Type u} (V : ι → C) :
    (∏ᶜ V) = ⨅ i, V i :=
  ((productIsProduct V).conePointUniqueUpToIso (Preorder.isLimitIInf V)).to_eq

instance inclusion_preserves {ι : Type u} [Finite ι] [Nonempty ι] (U : ι → X.affineOpens) [HasProduct U] :
    PreservesLimit (Discrete.functor U) (OpenProducts.AffineOpenProducts.inclusion X) := by
  let : IsIso (piComparison (OpenProducts.AffineOpenProducts.inclusion X) U) :=
    (PartialOrder.isIso_iff_eq _).mpr
      ((OpenProducts.AffineOpenProducts.product_eq X U).trans (product_iInf (fun i => (U i).val)).symm)
  exact PreservesProduct.of_iso_comparison _ _

variable (Y : Scheme.{u}) (f : Y ⟶ X)

instance preimage_preserves : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

instance composite_preserves {ι : Type u} [Finite ι] [Nonempty ι] (U : ι → X.affineOpens) [HasProduct U] :
    PreservesLimit (Discrete.functor U)
      (OpenProducts.AffineOpenProducts.inclusion X ⋙ Opens.map f.base) := by
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation.AffineOpenProductPreservation
