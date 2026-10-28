import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechKunneth

/-! # Cube Rectangle Cech Retractions -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCechRetractions.Construction.CubeCech

noncomputable section

/-! The rectangle Cech Kunneth calculation with specified splittings of the augmentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [UniversallyClosed f] [UniversallyClosed g]
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

theorem rectangleCech_boundary_of_split_augmentations
    (eC : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k] k)
    (eD : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V →ₗ[k] k)
    (heC : eC.comp (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U) = LinearMap.id)
    (heD : eD.comp (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation g V) = LinearMap.id)
    (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)
    (a : CubeRectangleCech.Construction.CubeCech.rectangleCech10 f g U V) (b : CubeRectangleCech.Construction.CubeCech.rectangleCech01 f g U V)
    (hmix : CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V a = CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V b)
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (ha : TensorProduct.map LinearMap.id eD
      ((CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).symm a) =
        OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x ⊗ₜ[k] (1 : k))
    (hb : TensorProduct.map eC LinearMap.id
      ((CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).symm b) =
        (1 : k) ⊗ₜ[k] OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y) :
    ∃ t : CubeRectangleCech.Construction.CubeCech.rectangleCech00 f g U V,
      CubeRectangleCech.Construction.CubeCech.rectangleCechD00h f g U V t = a ∧ CubeRectangleCech.Construction.CubeCech.rectangleCechD00v f g U V t = b := by
  let α := (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).symm a
  let β := (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).symm b
  have hαβ : TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) α =
      TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id β := by
    apply (CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV).injective
    rw [CubeRectangleCech.Construction.CubeCech.rectangleCechD10v_comparison f g U V hV hUU hVV α,
      CubeRectangleCech.Construction.CubeCech.rectangleCechD01h_comparison f g U V hU hUU hVV β]
    simpa only [α, β, LinearEquiv.apply_symm_apply] using hmix
  obtain ⟨t, htC, htD⟩ := CubeKunnethDegreeOne.Construction.CubeCech.tensor_degreeOne_boundary_of_exact_restrictions
    (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U) (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation g V) eC eD _ _ heC heD
    (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation_exact f U hcoverU) (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation_exact g V hcoverV)
    α β hαβ x y ha hb
  refine ⟨CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV t, ?_, ?_⟩
  · exact (CubeRectangleCech.Construction.CubeCech.rectangleCechD00h_comparison f g U V hU hV hUU t).symm.trans
      ((congrArg (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU) htC).trans
        ((CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).apply_symm_apply a))
  · exact (CubeRectangleCech.Construction.CubeCech.rectangleCechD00v_comparison f g U V hU hV hVV t).symm.trans
      ((congrArg (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV) htD).trans
        ((CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).apply_symm_apply b))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCechRetractions.Construction.CubeCech
