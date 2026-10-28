import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Zero Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ZeroInjection.ZariskiCohomology

noncomputable section

/-! A monomorphism of module sheaves induces an injection on genuine degree-zero coefficient cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem coefficientCohomology_zero_injective {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N) [hf : Mono f] :
    Function.Injective ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).map f).hom := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (.op ⊤)
  have hmono : Mono (F.map f) := @Functor.map_mono _ _ _ _ F _ N M f hf
  intro x y hxy
  apply (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).injective
  apply (ModuleCat.mono_iff_injective (f.val.app (.op ⊤))).mp hmono
  change f.app ⊤ (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M x) = f.app ⊤ (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M y)
  exact (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections_naturality f x).trans
    ((congrArg (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections N) hxy).trans
      (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections_naturality f y).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ZeroInjection.ZariskiCohomology
