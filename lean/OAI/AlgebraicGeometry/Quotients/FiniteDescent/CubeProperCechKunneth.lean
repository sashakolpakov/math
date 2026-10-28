import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechAugmentation

/-! # Cube Proper Cech Kunneth -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechKunneth.Construction.CubeCech

noncomputable section

/-! The mixed degree-one Kunneth calculation for actual Cech cochains of proper schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [UniversallyClosed f] [UniversallyClosed g]
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

theorem properCech_tensor_boundary_of_exact_restrictions
    (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (a : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (b : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (hmix : TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) a =
      TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id b)
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (ha : TensorProduct.map LinearMap.id (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction g V) a =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x ⊗ₜ[k] (1 : k))
    (hb : TensorProduct.map (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction f U) LinearMap.id b =
      (1 : k) ⊗ₜ[k] OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y) :
    ∃ t : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V,
      TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id t = a ∧
        TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) t = b :=
  CubeKunnethDegreeOne.Construction.CubeCech.tensor_degreeOne_boundary_of_exact_restrictions
    (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U) (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation g V)
    (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction f U) (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction g V) _ _
    (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction_comp f U hU) (CubeProperCechAugmentation.Construction.CubeCech.properCechRetraction_comp g V hV)
    (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation_exact f U hU) (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation_exact g V hV)
    a b hmix x y ha hb

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechKunneth.Construction.CubeCech
