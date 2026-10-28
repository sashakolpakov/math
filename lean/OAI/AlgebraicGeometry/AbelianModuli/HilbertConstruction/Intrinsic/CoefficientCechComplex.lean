import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductEvaluationAdditive
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Coefficient Cech Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.CoefficientCechComplex

noncomputable section

/-! The native tuple-indexed Čech complex retains its actual coefficient-module structure. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientCechComplex (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj (Coefficient.ModulePresheaf.coefficientModulePresheaf c M)

def coefficientCechComplexFunctor (c : R →+* Γ(X, ⊤))
    {ι : Type u} (U : ι → X.Opens) : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c ⋙ cechComplexFunctor U

@[simp] theorem coefficientCechComplexFunctor_obj (c : R →+* Γ(X, ⊤))
    {ι : Type u} (U : ι → X.Opens) (M : X.Modules) :
    (coefficientCechComplexFunctor c U).obj M = coefficientCechComplex c M U := rfl

instance moduleCatNativeCechComplexFunctor_preservesZeroMorphisms
    {ι : Type u} (U : ι → X.Opens) :
    (cechComplexFunctor (A := ModuleCat.{u} R) U).PreservesZeroMorphisms where
  map_zero F G := by
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun _ ↦ 0) = 0
    refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Pi.map_π, comp_zero]
    exact zero_comp.symm

instance coefficientCechComplexFunctor_preservesZeroMorphisms
    (c : R →+* Γ(X, ⊤)) {ι : Type u} (U : ι → X.Opens) :
    (coefficientCechComplexFunctor c U).PreservesZeroMorphisms where
  map_zero M N := by
    change (cechComplexFunctor U).map ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map (0 : M ⟶ N)) = 0
    have h : (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map (0 : M ⟶ N) = 0 := rfl
    rw [h]
    exact Functor.map_zero _ _ _

def coefficientCechXIsoPi (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechComplex c M U).X n ≅
      ModuleCat.of R (∀ i : Fin (n + 1) → ι, Ordered.CoefficientCechTerms.coefficientCechFactor c M U n i) :=
  ModuleCat.piIsoPi _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.CoefficientCechComplex
