import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Submodule -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Submodule.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the periodic complex of an invariant submodule and quotient

The maps are the actual inclusion and quotient maps, in each degree.
Their short exactness is proved degreewise from the submodule quotient
sequence, allowing periodic Euler additivity to be applied to modules.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

def endomorphismPeriodicMap {N : Type v} [AddCommGroup N] [Module R N]
    (φ ψ : M →ₗ[R] M) (φ' ψ' : N →ₗ[R] N)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hφψ' : ψ'.comp φ' = 0) (hψφ' : φ'.comp ψ' = 0)
    (f : M →ₗ[R] N) (hfφ : φ'.comp f = f.comp φ) (hfψ : ψ'.comp f = f.comp ψ) :
    PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ ⟶
      PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ' where
  f _ := ModuleCat.ofHom f
  comm' := by
    intro i j hij
    cases i <;> cases j <;>
      simp_all [PeriodicComplex.BundleCycles.periodicComplexShape, PeriodicComplex.BundleCycles.endomorphismPeriodicComplex, ← ModuleCat.ofHom_comp]

variable (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (P : Submodule R M) (hPφ : ∀ x ∈ P, φ x ∈ P) (hPψ : ∀ x ∈ P, ψ x ∈ P)

include hφψ in
theorem periodicRestriction_comp_zero : (ψ.restrict hPψ).comp (φ.restrict hPφ) = 0 := by
  ext x
  exact LinearMap.congr_fun hφψ x.1

include hφψ in
theorem periodicQuotient_comp_zero :
    (P.mapQ P ψ hPψ).comp (P.mapQ P φ hPφ) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := P.mkQ_surjective x
  change P.mkQ (ψ (φ x)) = 0
  exact (congrArg P.mkQ (LinearMap.congr_fun hφψ x)).trans P.mkQ.map_zero

def periodicSubmoduleComplex : HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape :=
  PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (φ.restrict hPφ) (ψ.restrict hPψ)
    (periodicRestriction_comp_zero φ ψ hφψ P hPφ hPψ)
    (periodicRestriction_comp_zero ψ φ hψφ P hPψ hPφ)

def periodicQuotientComplex : HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape :=
  PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (P.mapQ P φ hPφ) (P.mapQ P ψ hPψ)
    (periodicQuotient_comp_zero φ ψ hφψ P hPφ hPψ)
    (periodicQuotient_comp_zero ψ φ hψφ P hPψ hPφ)

def periodicSubmoduleInclusion : periodicSubmoduleComplex φ ψ hφψ hψφ P hPφ hPψ ⟶
    PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ :=
  endomorphismPeriodicMap _ _ _ _ _ _ _ _ P.subtype rfl rfl

def periodicQuotientProjection : PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ ⟶
    periodicQuotientComplex φ ψ hφψ hψφ P hPφ hPψ :=
  endomorphismPeriodicMap _ _ _ _ _ _ _ _ P.mkQ
    (P.mapQ_mkQ P φ) (P.mapQ_mkQ P ψ)

def periodicSubmoduleSequence :
    ShortComplex (HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape) :=
  ShortComplex.mk (periodicSubmoduleInclusion φ ψ hφψ hψφ P hPφ hPψ)
    (periodicQuotientProjection φ ψ hφψ hψφ P hPφ hPψ) (by
      ext i x
      exact (Submodule.Quotient.mk_eq_zero P).mpr x.2)

theorem periodicSubmoduleSequence_shortExact :
    (periodicSubmoduleSequence φ ψ hφψ hψφ P hPφ hPψ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  apply ModuleCat.shortComplex_shortExact
  · exact LinearMap.exact_subtype_mkQ P
  · exact P.subtype_injective
  · exact P.mkQ_surjective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Submodule.BundleCycles
