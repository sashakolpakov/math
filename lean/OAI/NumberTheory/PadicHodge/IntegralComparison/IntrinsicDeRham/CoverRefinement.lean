import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement

/-! # Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CoverRefinement.Intrinsic

noncomputable section

/-! Refinement of native de Rham Čech totals agrees with the
literal module-valued refinement on top forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def bicomplexMap : CechComplex.Intrinsic.bicomplex R X U ⟶ CechComplex.Intrinsic.bicomplex R X V where
  f q := GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U)
    (FormalCoproduct.mk κ V) r ((CechComplex.Intrinsic.presheafComplex R X).X q)
  comm' q q' _ := (GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
    (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r ((CechComplex.Intrinsic.presheafComplex R X).d q q')).symm

def map : CechComplex.Intrinsic.total R X U ⟶ CechComplex.Intrinsic.total R X V :=
  HomologicalComplex₂.total.map (bicomplexMap R X U V r) (.up ℕ)

theorem rowIso_natural (q : ℕ) :
    (TopEdge.Intrinsic.rowIso R X U q).hom ≫ (bicomplexMap R X U V r).f q =
      ModuleCech.CoverRefinement.map R X U V r (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q) ≫
        (TopEdge.Intrinsic.rowIso R X V q).hom :=
  GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
    (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r
    ((CechComplex.Intrinsic.presheaves R X).map (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X q).hom)

theorem row_coordinates (q : ℕ) :
    (TopEdge.Intrinsic.rowIso R X U q).hom ≫ (bicomplexMap R X U V r).f q ≫ (TopEdge.Intrinsic.rowIso R X V q).inv =
      ModuleCech.CoverRefinement.map R X U V r (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q) := by
  rw [← Category.assoc, rowIso_natural, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] in
theorem top_row :
    TopEdgeMap.Intrinsic.rowMap R X X V U g (bicomplexMap R X U V r) =
      (HomologicalComplex.homologyMap
        (ModuleCech.CoverRefinement.map R X U V r (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)) g).hom := by
  have h := congrArg (fun a => HomologicalComplex.homologyMap a g) (row_coordinates R X U V r g)
  simp only [HomologicalComplex.homologyMap_comp] at h
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom h x

theorem top_edge (x : TopEdge.Intrinsic.source R X U g) :
    HomologicalComplex.homologyMap (Intrinsic.map R X U V r) (g + g)
      (TopEdge.Intrinsic.map R X U g x) =
    TopEdge.Intrinsic.map R X V g
      (HomologicalComplex.homologyMap
        (ModuleCech.CoverRefinement.map R X U V r (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)) g x) := by
  have h := TopEdgeMap.Intrinsic.naturality R X X V U g (bicomplexMap R X U V r) x
  rw [top_row R X U V r g] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CoverRefinement.Intrinsic
