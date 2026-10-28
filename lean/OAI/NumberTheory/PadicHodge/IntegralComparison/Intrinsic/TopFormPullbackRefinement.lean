import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback

/-! # Top Form Pullback Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormPullbackRefinement

noncomputable section

/-! The original pullback on a refined source cover is the
inverse-cover pullback followed by the literal module Čech refinement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate {C : Type*} [Category C] {A B D A' B' D' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D')
    (a : A' ⟶ B') (b : B' ⟶ D') (c : B ⟶ D)
    (h : eB.hom ≫ b = c ≫ eD.hom) :
    eA.hom ≫ (a ≫ b) ≫ eD.inv = (eA.hom ≫ a ≫ eB.inv) ≫ c := by
  have hc : b ≫ eD.inv = eB.inv ≫ c := by
    apply (cancel_epi eB.hom).1
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc]
  rw [hc]

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  {ι κ : Type u} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
local notation "W" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U

def refinement : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι W :=
  AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometric.RefinedGeometricCechPullback.coverMap X.left W V r hr

theorem row (q : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f U V r hr).f q =
      (IntrinsicDeRham.CechTransfer.Intrinsic.pullback R X Y f U).f q ≫
        GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι W) (FormalCoproduct.mk κ V)
          (refinement R X Y f U V r hr) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X q).obj :=
  (Category.assoc _ _ _).symm

theorem conjugated_row (q : ℕ) :
    (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R Y U q).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f U V r hr).f q ≫
        (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X V q).inv =
    ((IntrinsicDeRham.TopEdge.Intrinsic.rowIso R Y U q).hom ≫
      (IntrinsicDeRham.CechTransfer.Intrinsic.pullback R X Y f U).f q ≫
        (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X W q).inv) ≫
          ModuleCech.CoverRefinement.map R X W V (refinement R X Y f U V r hr)
            (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q) := by
  rw [row]
  exact conjugate
    (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R Y U q)
    (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X W q)
    (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X V q) _ _ _
    (GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality (FormalCoproduct.mk ι W) (FormalCoproduct.mk κ V)
      (refinement R X Y f U V r hr)
      ((IntrinsicDeRham.CechComplex.Intrinsic.presheaves R X).map
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X q).hom))

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom]

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom] in
theorem pullback (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y U g) :
    IntrinsicDeRham.TopEdgeMap.Intrinsic.rowMap R X Y V U g
      (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f U V r hr) x =
    HomologicalComplex.homologyMap (ModuleCech.CoverRefinement.map R X W V
      (refinement R X Y f U V r hr) (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)) g
        (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.pullback R X Y f U g x) := by
  have h := congrArg (fun z => HomologicalComplex.homologyMap z g)
    (conjugated_row R X Y f U V r hr g)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormPullbackRefinement
