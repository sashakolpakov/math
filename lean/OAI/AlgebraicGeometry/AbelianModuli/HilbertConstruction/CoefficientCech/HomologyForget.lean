import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ForgetNaturality
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Homology Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyForget

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

/-- Forgetting the base-module structure on Cech homology recovers the
homology of the native additive Cech complex. -/
noncomputable def coefficientCechComplexHomologyForgetIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (Module.ProductForget.moduleForget R).obj ((Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).homology n) ≅
      ((cechComplexFunctor U).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj).homology n :=
  (((Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).sc n).mapHomologyIso
    (Module.ProductForget.moduleForget R)).symm ≪≫
      HomologicalComplex.homologyMapIso
        (ComplexForget.coefficientCechComplexForgetIso ρ M U) n

/-- The forward map of the forgetful homology comparison is the mapped-homology
comparison followed by the homology map of the degreewise forgetful isomorphism. -/
@[simp]
theorem coefficientCechComplexHomologyForgetIso_hom
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechComplexHomologyForgetIso ρ M U n).hom =
      (((Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).sc n).mapHomologyIso
          (Module.ProductForget.moduleForget R)).inv ≫
        HomologicalComplex.homologyMap
          (ComplexForget.coefficientCechComplexForgetIso ρ M U).hom n :=
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyForget
