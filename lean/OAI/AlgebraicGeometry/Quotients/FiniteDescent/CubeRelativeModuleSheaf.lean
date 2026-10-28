import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperGlobalSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechDegreeZero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLineBundle
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Cube Relative Module Sheaf -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech

noncomputable section

/-! Sheaves of base-field vector spaces underlying modules on a scheme over that field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

def modulesAsBaseFieldSheaf : X.Modules ⥤
    TopCat.Sheaf (ModuleCat.{u} k) (Scheme.forgetToTop.obj X) := by
  let H := ModuleCat.restrictScalars.{u} (CubeProperGlobalSections.Construction.CubeCech.globalConstants f)
  have hH : (_root_.Opens.grothendieckTopology X).HasSheafCompose H :=
    hasSheafCompose_of_preservesLimitsOfSize (J := _root_.Opens.grothendieckTopology X) (F := H)
  exact SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
      @sheafCompose _ _ _ _ _ _ (_root_.Opens.grothendieckTopology X) H hH

abbrev structureSheafAsBaseFieldSheaf :=
  (modulesAsBaseFieldSheaf f).obj (CubeLineBundle.Construction.CubeCech.structureSheafModule X)

def globalConstantsLinearMap : k →ₗ[k] (structureSheafAsBaseFieldSheaf f).obj.obj (op ⊤) where
  toFun := CubeProperGlobalSections.Construction.CubeCech.globalConstants f
  map_add' := (CubeProperGlobalSections.Construction.CubeCech.globalConstants f).map_add
  map_smul' a b := by
    change CubeProperGlobalSections.Construction.CubeCech.globalConstants f (a * b) =
      X.presheaf.map (𝟙 (op ⊤)) (CubeProperGlobalSections.Construction.CubeCech.globalConstants f a) * CubeProperGlobalSections.Construction.CubeCech.globalConstants f b
    rw [X.presheaf.map_id]
    exact (CubeProperGlobalSections.Construction.CubeCech.globalConstants f).map_mul a b

theorem globalConstantsLinearMap_bijective [IsAlgClosed k] [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (globalConstantsLinearMap f) := CubeProperGlobalSections.Construction.CubeCech.globalConstants_bijective f

def properGlobalSectionsLinearEquiv [IsAlgClosed k] [IsIntegral X] [UniversallyClosed f] :
    k ≃ₗ[k] (structureSheafAsBaseFieldSheaf f).obj.obj (op ⊤) :=
  LinearEquiv.ofBijective (globalConstantsLinearMap f) (globalConstantsLinearMap_bijective f)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech
