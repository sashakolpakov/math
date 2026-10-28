import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSectionsBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections

/-! # Pullback Module Charts -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts.Construction

noncomputable section

/-! Canonical tensor pullback on specified trivializing charts of a line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)

def modulePullbackOpenComparison :
    (Scheme.Modules.pullback (f.resLE U V hVU)).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackComp (f.resLE U V hVU) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (f.resLE_comp_ι hVU)).app M ≪≫
    ((Scheme.Modules.pullbackComp V.ι f).app M).symm

def pullbackLineBundleChart
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj M) ≅
      LineBundle.Construction.structureSheafModule V.toScheme :=
  (modulePullbackOpenComparison f M U V hVU).symm ≪≫
    (Scheme.Modules.pullback (f.resLE U V hVU)).mapIso e ≪≫
    LineBundle.Construction.pullbackStructureSheafIso (f.resLE U V hVU)

def modulePullbackChartTensorEquiv
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := (f.resLE U V hVU).appTop.hom.toAlgebra
    (Γ(V, ⊤) ⊗[Γ(U, ⊤)] Γ((Scheme.Modules.pullback U.ι).obj M, ⊤)) ≃ₗ[Γ(V, ⊤)]
      Γ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj M), ⊤) := by
  letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := (f.resLE U V hVU).appTop.hom.toAlgebra
  exact (ModuleSectionsBaseChange.Construction.trivialModuleSectionsBaseChangeEquiv (f.resLE U V hVU) e).trans
    (PullbackTensorNaturality.Construction.moduleGlobalSectionsIso (modulePullbackOpenComparison f M U V hVU))

theorem modulePullbackChartTensorEquiv_eq_canonical
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := (f.resLE U V hVU).appTop.hom.toAlgebra
    (modulePullbackChartTensorEquiv f M U V hVU e).toLinearMap =
      (PullbackTensorNaturality.Construction.moduleGlobalSectionsIso (modulePullbackOpenComparison f M U V hVU)).toLinearMap.comp
        (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)) := by
  let : Algebra Γ(U, ⊤) Γ(V, ⊤) := (f.resLE U V hVU).appTop.hom.toAlgebra
  rw [ModuleSectionsBaseChange.Construction.modulePullbackSectionsTensorMap_trivial_eq (f.resLE U V hVU) e]
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts.Construction
