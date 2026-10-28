import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation

/-! # Open Finite Product Preservation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation

noncomputable section

/-! Affine-open inclusion and geometric inverse image preserve finite nonempty products with arbitrary index universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable (X : Scheme.{u}) [X.IsSeparated]

theorem product_eq {ι : Type v} [Finite ι] [Nonempty ι] (U : ι → X.affineOpens) [HasProduct U] :
    (∏ᶜ U).val = ⨅ i, (U i).val := by
  apply le_antisymm
  · exact le_iInf fun i => leOfHom (Pi.π U i)
  · let V : X.affineOpens := ⟨⨅ i, (U i).val, IsAffineOpen.iInf (fun i => (U i).property)⟩
    exact leOfHom (Pi.lift (P := V) (fun i => homOfLE (iInf_le (fun j => (U j).val) i)))

theorem product_iInf {C : Type u} [CompleteLattice C] {ι : Type v} (V : ι → C) :
    (∏ᶜ V) = ⨅ i, V i :=
  ((productIsProduct V).conePointUniqueUpToIso (Preorder.isLimitIInf V)).to_eq

theorem inclusion_preserves {ι : Type v} [Finite ι] [Nonempty ι] (U : ι → X.affineOpens) [HasProduct U] :
    PreservesLimit (Discrete.functor U) (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X) := by
  let : IsIso (piComparison (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X) U) :=
    (PartialOrder.isIso_iff_eq _).mpr ((product_eq X U).trans (product_iInf (fun i => (U i).val)).symm)
  exact PreservesProduct.of_iso_comparison _ _

theorem composite_preserves (Y : Scheme.{u}) (f : Y ⟶ X)
    {ι : Type v} [Finite ι] [Nonempty ι] (U : ι → X.affineOpens) [HasProduct U] :
    PreservesLimit (Discrete.functor U) (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X ⋙ Opens.map f.base) := by
  let : PreservesLimit (Discrete.functor U) (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X) := inclusion_preserves X U
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation
