import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomScalar

/-! # Sheaf Hom Module -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction

noncomputable section

/-! Local module homomorphisms form a sheaf of modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance moduleHomAbSectionsModule {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((ModuleHomAdditive.Construction.moduleHomAbPresheaf M N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U.unop))

theorem moduleHomAbPresheaf_map_smul {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (r : X.ringCatSheaf.obj.obj U)
    (q : (ModuleHomAdditive.Construction.moduleHomAbPresheaf M N).obj U) :
    (ModuleHomAdditive.Construction.moduleHomAbPresheaf M N).map f (r • q) =
      X.ringCatSheaf.obj.map f r • (ModuleHomAdditive.Construction.moduleHomAbPresheaf M N).map f q := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  ext m
  let z : Γ(N, W.unop.left) := q.1.app (.op ((Over.map f.unop).obj W.unop)) m
  change X.presheaf.map (W.unop.hom ≫ f.unop).op r • z =
    X.presheaf.map W.unop.hom.op (X.presheaf.map f r) • z
  have hr := congrArg (fun a ↦ a r) (X.presheaf.map_comp f W.unop.hom.op)
  exact congrArg (fun a ↦ a • z) hr

def sheafHomModulePresheaf {X : Scheme.{u}} (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj) (ModuleHomAdditive.Construction.moduleHomAbPresheaf M N)
    (fun {_ _} f r q ↦ moduleHomAbPresheaf_map_smul M N f r q)

def sheafHomModule {X : Scheme.{u}} (M N : X.Modules) : X.Modules where
  val := sheafHomModulePresheaf M N
  isSheaf := (ModuleHomAdditive.Construction.moduleHomAbSheaf M N).property

def lineBundleDual {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  sheafHomModule M (LineBundle.Construction.structureSheafModule X)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction
