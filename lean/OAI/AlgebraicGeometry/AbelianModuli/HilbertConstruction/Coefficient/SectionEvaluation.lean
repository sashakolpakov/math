import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Section Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionEvaluation

noncomputable section

/-! Coefficient section evaluation is native section evaluation followed by restriction of scalars. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientSectionFunctor (c : R →+* Γ(X, ⊤)) (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} R :=
  ModulePresheafFunctor.coefficientModulePresheafFunctor c ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)

def coefficientSectionEvaluationIso (c : R →+* Γ(X, ⊤)) (U : X.Opens) :
    coefficientSectionFunctor c U ≅
      SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        ModuleCat.restrictScalars ((X.presheaf.map U.leTop.op).hom.comp c) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, U))
    rfl
  · intro M N f
    apply ModuleCat.hom_ext
    ext x
    rfl

instance coefficientSectionFunctor_preservesFiniteLimits (c : R →+* Γ(X, ⊤)) (U : X.Opens) :
    PreservesFiniteLimits (coefficientSectionFunctor c U) := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let G : ModuleCat.{u} Γ(X, U) ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars ((X.presheaf.map U.leTop.op).hom.comp c)
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  have : PreservesFiniteLimits G := by dsimp [G]; infer_instance
  have : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  let e : coefficientSectionFunctor c U ≅ F ⋙ G := coefficientSectionEvaluationIso c U
  exact preservesFiniteLimits_of_natIso e.symm

instance coefficientSectionFunctor_additive (c : R →+* Γ(X, ⊤)) (U : X.Opens) :
    (coefficientSectionFunctor c U).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    ext x
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionEvaluation
