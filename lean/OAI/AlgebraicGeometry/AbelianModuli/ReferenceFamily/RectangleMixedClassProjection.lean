import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedComplexBoundaryProjection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex

/-! # Rectangle Mixed Class Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleMixedClassProjection

noncomputable section

/-! Actual affine rectangle sections have a mixed projection to
the tensor of the two degree-one cycle quotients. The original
horizontal and vertical Cech boundaries are annihilated. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

variable {k : Type} [Field k]

abbrev openModuleCycleQuotient {T : TopCat.{0}}
    (F : TopCat.Sheaf (ModuleCat.{0} k) T) {I : Type} (U : I → Opens T) :=
  LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 F U) ⧸
    MixedComplexBoundaryProjection.cycleBoundarySubmodule (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F U) (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 F U)

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : I → X.Opens) (V : J → Y.Opens)
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

def rectangleMixedClassProjection : Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCech11 f g U V →ₗ[k]
    openModuleCycleQuotient (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      openModuleCycleQuotient (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V :=
  (TensorProduct.map
    (MixedComplexBoundaryProjection.cycleClassProjection (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
      (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U))
    (MixedComplexBoundaryProjection.cycleClassProjection (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
      (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V))).comp
        (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).symm.toLinearMap

theorem rectangleMixedClassProjection_cycles
    (x : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U))
    (y : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)) :
    rectangleMixedClassProjection f g U V hUU hVV
      (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV (x.val ⊗ₜ[k] y.val)) =
      (MixedComplexBoundaryProjection.cycleBoundarySubmodule (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
        (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)).mkQ x ⊗ₜ[k]
      (MixedComplexBoundaryProjection.cycleBoundarySubmodule (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
        (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)).mkQ y := by
  change TensorProduct.map _ _ ((Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).symm
    (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV (x.val ⊗ₜ[k] y.val))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  exact congrArg₂ (fun a b => a ⊗ₜ[k] b)
    (MixedComplexBoundaryProjection.cycleClassProjection_cycle
      (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
      (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) x)
    (MixedComplexBoundaryProjection.cycleClassProjection_cycle
      (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
      (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) y)

theorem rectangleMixedClassProjection_boundary
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (a : Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCech10 f g U V) (b : Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCech01 f g U V) :
    rectangleMixedClassProjection f g U V hUU hVV
      (Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V a - Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V b) = 0 := by
  let α := (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).symm a
  let β := (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).symm b
  have h : (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).symm
      (Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V a - Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V b) =
    TensorProduct.map LinearMap.id (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) α -
      TensorProduct.map (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id β := by
    apply (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).injective
    rw [LinearEquiv.apply_symm_apply, map_sub,
      Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD10v_comparison f g U V hV hUU hVV,
      Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD01h_comparison f g U V hU hUU hVV]
    exact congrArg₂ (· - ·)
      (congrArg (Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V)
        ((Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).apply_symm_apply a).symm)
      (congrArg (Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V)
        ((Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).apply_symm_apply b).symm)
  change TensorProduct.map _ _ ((Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).symm _) = 0
  rw [h]
  exact MixedComplexBoundaryProjection.mixedComplexBoundary_projection_zero _ _
    (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_comp_D0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) _ _
    (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_comp_D0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) α β

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleMixedClassProjection
