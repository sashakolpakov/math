import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule

/-! # Sheaf Hom Evaluation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction

noncomputable section

/-! Evaluation of local module homomorphisms on sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance homEvaluationPresheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance homEvaluationSectionsModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (.op U)) := (M.val.obj (.op U)).isModule

local instance homEvaluationOpSectionsModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule

def sheafHomEvalAtOpen {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    (SheafHomModule.Construction.sheafHomModule M N).val.obj (.op U) →ₗ[Γ(X, U)]
      (M.val.obj (.op U) →ₗ[Γ(X, U)] N.val.obj (.op U)) where
  toFun q := ((ModuleHomSheaf.Construction.moduleHomToOver M N U q).val.app (.op (Over.mk (𝟙 U)))).hom
  map_add' q q' := by ext m; rfl
  map_smul' r q := by
    ext m
    let z : Γ(N, U) := q.1.app (.op (Over.mk (𝟙 U))) m
    change X.presheaf.map (𝟙 U).op r • z = r • z
    simp

def sheafHomEvalPresheaf {X : Scheme.{u}} (M N : X.Modules) :
    (SheafHomModule.Construction.sheafHomModule M N).val ⊗ M.val ⟶ N.val where
  app U := ModuleCat.ofHom (R := Γ(X, U.unop))
    (X := ((SheafHomModule.Construction.sheafHomModule M N).val.obj U ⊗ M.val.obj U : ModuleCat Γ(X, U.unop)))
    (Y := N.val.obj U) (TensorProduct.lift (sheafHomEvalAtOpen M N U.unop))
  naturality {U V} h := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro q m
    let j : Over.mk h.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk h.unop
    exact congrArg (fun a ↦ a m) (q.1.naturality j.op)

def sheafHomEvaluation {X : Scheme.{u}} (M N : X.Modules) :
    SheafTensor.Construction.sheafTensor (SheafHomModule.Construction.sheafHomModule M N) M ⟶ N :=
  (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).symm (sheafHomEvalPresheaf M N)

theorem sheafHomEvaluation_homEquiv {X : Scheme.{u}} (M N : X.Modules) :
    SheafTensor.Construction.sheafTensorHomEquiv _ _ _ (sheafHomEvaluation M N) = sheafHomEvalPresheaf M N :=
  (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).apply_symm_apply _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction
