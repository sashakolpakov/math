/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCech.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.CosimplicialForget

/-! # Complex Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ComplexForget

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

theorem coefficientCechComplex_d_succ
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (i : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).d
      i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

theorem cechComplex_d_succ
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (i : ℕ) :
    ((cechComplexFunctor U).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj).d i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

theorem coefficientCechCosimplicialIso_comm_d
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (i : ℕ) :
    (CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.app (SimplexCategory.mk i) ≫
        AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor
            (FormalCoproduct.mk _ U).cech).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj) i =
      (Module.ProductForget.moduleForget R).map
          (AlternatingCofaceMapComplex.objD
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj
                (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)) i) ≫
        (CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.app
          (SimplexCategory.mk (i + 1)) := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    ((CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.naturality
      (SimplexCategory.δ k)).symm

/-- Forgetting the base module structure on `coefficientCechComplex` gives the native
additive Cech complex of the underlying sheaf. -/
noncomputable def coefficientCechComplexForgetIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (((Module.ProductForget.moduleForget R).mapHomologicalComplex (.up ℕ)).obj
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U)) ≅
        (cechComplexFunctor U).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (CosimplicialForget.coefficientCechCosimplicialIso ρ M U).app (SimplexCategory.mk n)) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Functor.mapHomologicalComplex_obj_d]
      rw [coefficientCechComplex_d_succ, cechComplex_d_succ]
      exact coefficientCechCosimplicialIso_comm_d ρ M U i)

@[simp]
theorem coefficientCechComplexForgetIso_hom_f
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechComplexForgetIso ρ M U).hom.f n =
      (CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.app (SimplexCategory.mk n) :=
  rfl

/-- The forgetful complex comparison preserves every concrete intersection component. -/
theorem coefficientCechComplexForgetIso_component
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    (coefficientCechComplexForgetIso ρ M U).hom.f n ≫
        Pi.π (fun a : Fin (n + 1) → ι =>
          M.presheaf.obj (op (∏ᶜ fun k : Fin (n + 1) => U (a k)))) i =
      (Module.ProductForget.moduleForget R).map
        (Pi.π (fun a : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n a) i) := by
  rw [coefficientCechComplexForgetIso_hom_f]
  exact CosimplicialForget.coefficientCechCosimplicialIso_hom_π ρ M U (SimplexCategory.mk n) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ComplexForget
