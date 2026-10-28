import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.HolomorphicNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf

/-! # Analytified Form -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedForm

noncomputable section

section

/-! The actual algebraic differential modules map to the actual holomorphic differential modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

abbrev analyticHolomorphicFormModuleSheaf (n : ℕ) :
    SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) :=
  ManifoldHolomorphicModuleSheaf.manifoldHolomorphicFormModuleSheaf (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n

def zariskiHolomorphicFormModuleSheaf (n : ℕ) : SheafOfModules.{0} X.left.ringCatSheaf :=
  (Holomorphic.StructureMorphism.holomorphicModuleDirectImage X).obj (analyticHolomorphicFormModuleSheaf X n)

def exteriorToHolomorphicModuleApp (U : (Opens X.left)ᵒᵖ) (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj U ⟶ (zariskiHolomorphicFormModuleSheaf X n).val.obj U :=
  ModuleCat.ofHom (R := X.left.ringCatSheaf.obj.obj U)
    (X := (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj U)
    (Y := (zariskiHolomorphicFormModuleSheaf X n).val.obj U)
    { toFun := Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap X U.unop n
      map_add' := (Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap X U.unop n).map_add
      map_smul' := (Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap X U.unop n).map_smulₛₗ }

def exteriorToHolomorphicModulePresheafMap (n : ℕ) :
    Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n ⟶ (zariskiHolomorphicFormModuleSheaf X n).val where
  app U := exteriorToHolomorphicModuleApp X U n
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Exterior.HolomorphicNaturality.exteriorToHolomorphicFormMap_restrict X (leOfHom f.unop) n a

def exteriorToHolomorphicModuleSheafMap (n : ℕ) :
    Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n ⟶ zariskiHolomorphicFormModuleSheaf X n :=
  ((PresheafOfModules.sheafificationAdjunction.{0} (R := X.left.ringCatSheaf)
    (𝟙 X.left.ringCatSheaf.obj)).homEquiv
      (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n) (zariskiHolomorphicFormModuleSheaf X n)).symm
        (exteriorToHolomorphicModulePresheafMap X n)

theorem exteriorToHolomorphicModuleSheafMap_normalization (n : ℕ) :
    (PresheafOfModules.sheafificationAdjunction.{0} (R := X.left.ringCatSheaf)
      (𝟙 X.left.ringCatSheaf.obj)).homEquiv _ _ (exteriorToHolomorphicModuleSheafMap X n) =
        exteriorToHolomorphicModulePresheafMap X n :=
  Equiv.apply_symm_apply _ _

theorem exteriorToHolomorphicModuleApp_normalization (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    exteriorToHolomorphicModuleApp X (op U) n
        (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n a) =
      (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a :=
  Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap_normalization X U n a

def analytifiedExteriorToHolomorphicModuleMap (n : ℕ) :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) ⟶
      analyticHolomorphicFormModuleSheaf X n :=
  ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).homEquiv
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) (analyticHolomorphicFormModuleSheaf X n)).symm
      (exteriorToHolomorphicModuleSheafMap X n)

theorem analytifiedExteriorToHolomorphicModuleMap_adjunction (n : ℕ) :
    (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).homEquiv _ _
      (analytifiedExteriorToHolomorphicModuleMap X n) = exteriorToHolomorphicModuleSheafMap X n :=
  Equiv.apply_symm_apply _ _

end

section

/-! Original algebraic forms have actual sections in the analytified source, with the exact comparison image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def exteriorFormSheafSection (U : X.left.Opens) (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (R := X.left.ringCatSheaf)
    (𝟙 X.left.ringCatSheaf.obj)).unit.app (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n)).app (op U)
      (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n a)

def analytifiedFormSection (U : X.left.Opens) (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen X U)) :=
  ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.app
    (op U) (exteriorFormSheafSection X U n a)

theorem exteriorFormSheafSection_comparison (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (exteriorToHolomorphicModuleSheafMap X n).val.app (op U) (exteriorFormSheafSection X U n a) =
      (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.left.ringCatSheaf)
    (𝟙 X.left.ringCatSheaf.obj)
  have h := (adj.homEquiv_unit _ _ (exteriorToHolomorphicModuleSheafMap X n)).symm.trans
    (exteriorToHolomorphicModuleSheafMap_normalization X n)
  have hv := congrArg (fun k => k.app (op U) (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n a)) h
  exact hv.trans (exteriorToHolomorphicModuleApp_normalization X U n a)

theorem analytifiedFormSection_comparison (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (analytifiedExteriorToHolomorphicModuleMap X n).val.app (op (Open.AffineIsoEvaluation.analyticOpen X U))
        (analytifiedFormSection X U n a) = (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a := by
  have h := ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).homEquiv_unit _ _
    (analytifiedExteriorToHolomorphicModuleMap X n)).symm.trans
      (analytifiedExteriorToHolomorphicModuleMap_adjunction X n)
  have hv := congrArg (fun k => k.val.app (op U) (exteriorFormSheafSection X U n a)) h
  exact hv.trans (exteriorFormSheafSection_comparison X U n a)

end

/-! Actual algebraic-image sections lift through the analytified map on every smaller analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analytifiedFormSectionOn (U : X.left.Opens) (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U) (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W) :=
  ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.map
    (homOfLE hW).op (analytifiedFormSection X U n a)

theorem analytifiedFormSectionOn_comparison (U : X.left.Opens) (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U) (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (analytifiedExteriorToHolomorphicModuleMap X n).val.app (op W)
        (analytifiedFormSectionOn X U W hW n a) =
      Holomorphic.HolomorphicPullback.pullback (Opens.inclusion hW)
        (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) hW) n
          ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  have h := PresheafOfModules.naturality_apply (analytifiedExteriorToHolomorphicModuleMap X n).val
    (homOfLE hW).op (analytifiedFormSection X U n a)
  exact h.trans (congrArg ((analyticHolomorphicFormModuleSheaf X n).val.map (homOfLE hW).op)
    (analytifiedFormSection_comparison X U n a))

end

end OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedForm
