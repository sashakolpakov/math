import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFinite
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarExtension

/-! # Flat Filtered -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered.FlatFilteredTotalCohomology

noncomputable section

/-! Flat scalar extension preserves the outer-degree filtration on actual Čech total cohomology. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable {R : Type} [CommRing R] (K : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ))

def filtrationMap (n r : ℤ) : ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).homology n →ₗ[R]
    ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj K).homology n :=
  (HomologicalComplex.homologyMap ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) n).hom

def filtration (n r : ℤ) : Submodule R (((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj K).homology n) :=
  LinearMap.range (filtrationMap K n r)

variable {S : Type} [CommRing S] [Algebra R S] [Module.Flat R S]
  (L : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ))
  (e : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (FlatScalar.FlatScalarExtension.moduleFunctor R S) K ≅ L)

def comparison (n : ℤ) : S ⊗[R] ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj K).homology n ≃ₗ[S] ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)).obj L).homology n :=
  (ExactHomology.ExactHomologyComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ) ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj K) ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)).obj L) (TotalFinite.TotalScalarComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) e) n).toLinearEquiv

def truncatedComparison (n r : ℤ) : S ⊗[R] ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).homology n ≃ₗ[S]
    ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r)).homology n :=
  (ExactHomology.ExactHomologyComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ) ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r))
    ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r))
    (TotalFinite.TotalScalarComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (TruncatedFunctorIso.TruncatedPullback.iso ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)) e r)) n).toLinearEquiv

theorem filtrationMap_square (n r : ℤ) (x : S ⊗[R] ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).homology n) :
    comparison K L e n ((filtrationMap K n r).baseChange S x) =
      filtrationMap L n r (truncatedComparison K L e n r x) :=
  congrArg (fun f => f x)
    (ExactHomology.ExactHomologyComparison.naturality (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ)
      (TotalFinite.TotalScalarComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (TruncatedFunctorIso.TruncatedPullback.iso ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)) e r))
      (TotalFinite.TotalScalarComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) e) ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r))
      ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r))
      (TotalFinite.TotalScalarComparison.naturality (FlatScalar.FlatScalarExtension.moduleFunctor R S) (TruncatedFunctorIso.TruncatedPullback.iso ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)) e r) e
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r)
        (TruncatedFunctorIso.TruncatedPullback.iso_inclusion ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)) e r).symm) n)

theorem filtration_eq (n r : ℤ) :
    ((filtration K n r).baseChange S).map (comparison K L e n).toLinearMap = filtration L n r := by
  rw [filtration, ScalarExtension.ScalarExtensionRanges.range]
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨truncatedComparison K L e n r x, (filtrationMap_square K L e n r x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (truncatedComparison K L e n r).surjective x
    exact ⟨(filtrationMap K n r).baseChange S z, ⟨z, rfl⟩, filtrationMap_square K L e n r z⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered.FlatFilteredTotalCohomology
