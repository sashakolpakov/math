import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeModuleSheaf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeKunnethDegreeOne

/-! # Cube Proper Cech Augmentation -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechAugmentation.Construction.CubeCech

noncomputable section

/-! Actual augmented Cech complexes of proper integral schemes have the required contraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {ι : Type v} (U : ι → X.Opens)

def properCechAugmentation : k →ₗ[k] OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U :=
  (OpenCechDegreeZero.Construction.CubeCech.openModuleCechUnit (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U).comp (CubeRelativeModuleSheaf.Construction.CubeCech.globalConstantsLinearMap f)

def properCechRetraction : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k] k :=
  (properCechAugmentation f U).leftInverse

variable [IsAlgClosed k] [IsIntegral X] [UniversallyClosed f]

theorem properCechAugmentation_exact (hU : iSup U = ⊤) :
    Function.Exact (properCechAugmentation f U)
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) := by
  intro x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := (OpenCechDegreeZero.Construction.CubeCech.openModuleCech_exact_degreeZero (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U hU x).mp hx
    obtain ⟨r, rfl⟩ := (CubeRelativeModuleSheaf.Construction.CubeCech.globalConstantsLinearMap_bijective f).surjective s
    exact ⟨r, hs⟩
  · rintro ⟨r, rfl⟩
    exact (OpenCechDegreeZero.Construction.CubeCech.openModuleCech_exact_degreeZero (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U hU _).mpr
      ⟨CubeRelativeModuleSheaf.Construction.CubeCech.globalConstantsLinearMap f r, rfl⟩

theorem properCechAugmentation_injective (hU : iSup U = ⊤) :
    Function.Injective (properCechAugmentation f U) :=
  (OpenCechDegreeZero.Construction.CubeCech.openModuleCechUnit_injective (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U hU).comp
    (CubeRelativeModuleSheaf.Construction.CubeCech.globalConstantsLinearMap_bijective f).injective

theorem properCechRetraction_comp (hU : iSup U = ⊤) :
    (properCechRetraction f U).comp (properCechAugmentation f U) = LinearMap.id :=
  LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr (properCechAugmentation_injective f U hU))

theorem properCech_contraction_exists (hU : iSup U = ⊤) :
    ∃ h : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U,
      h.comp (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) =
        LinearMap.id - (properCechAugmentation f U).comp (properCechRetraction f U) :=
  CubeVectorSpaceContraction.Construction.CubeCech.augmented_vectorSpace_contraction _ _ _ (properCechRetraction_comp f U hU)
    (properCechAugmentation_exact f U hU)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechAugmentation.Construction.CubeCech
