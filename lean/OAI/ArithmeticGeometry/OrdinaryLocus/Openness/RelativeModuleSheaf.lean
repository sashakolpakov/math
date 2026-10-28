import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperGlobalSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Relative Module Sheaf -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeModuleSheaf.Construction

noncomputable section

/-! Sheaves of base-field vector spaces underlying modules on a scheme over that field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

def modulesAsBaseFieldSheaf : X.Modules ⥤
    TopCat.Sheaf (ModuleCat.{u} k) (Scheme.forgetToTop.obj X) := by
  let H := ModuleCat.restrictScalars.{u} (ProperGlobalSections.Construction.globalConstants f)
  have hH : (_root_.Opens.grothendieckTopology X).HasSheafCompose H :=
    hasSheafCompose_of_preservesLimitsOfSize (J := _root_.Opens.grothendieckTopology X) (F := H)
  exact SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
      @sheafCompose _ _ _ _ _ _ (_root_.Opens.grothendieckTopology X) H hH

abbrev structureSheafAsBaseFieldSheaf :=
  (modulesAsBaseFieldSheaf f).obj (LineBundle.Construction.structureSheafModule X)

def globalConstantsLinearMap : k →ₗ[k] (structureSheafAsBaseFieldSheaf f).obj.obj (op ⊤) where
  toFun := ProperGlobalSections.Construction.globalConstants f
  map_add' := (ProperGlobalSections.Construction.globalConstants f).map_add
  map_smul' a b := by
    change ProperGlobalSections.Construction.globalConstants f (a * b) =
      X.presheaf.map (𝟙 (op ⊤)) (ProperGlobalSections.Construction.globalConstants f a) * ProperGlobalSections.Construction.globalConstants f b
    rw [X.presheaf.map_id]
    exact (ProperGlobalSections.Construction.globalConstants f).map_mul a b

theorem globalConstantsLinearMap_bijective [IsAlgClosed k] [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (globalConstantsLinearMap f) := ProperGlobalSections.Construction.globalConstants_bijective f

def properGlobalSectionsLinearEquiv [IsAlgClosed k] [IsIntegral X] [UniversallyClosed f] :
    k ≃ₗ[k] (structureSheafAsBaseFieldSheaf f).obj.obj (op ⊤) :=
  LinearEquiv.ofBijective (globalConstantsLinearMap f) (globalConstantsLinearMap_bijective f)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeModuleSheaf.Construction
