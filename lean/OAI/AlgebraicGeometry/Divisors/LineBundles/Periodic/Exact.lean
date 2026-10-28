import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex

/-! # Exact -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the explicit kernel modulo image of a periodic complex
-/

open _root_.CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The image of the incoming map as a submodule of the outgoing kernel. -/
def periodicBoundaryMap (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) :
    M →ₗ[R] φ.ker :=
  ψ.codRestrict φ.ker (fun x => LinearMap.congr_fun hψφ x)

abbrev periodicHomology (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) :=
  φ.ker ⧸ (periodicBoundaryMap φ ψ hψφ).range

def endomorphismPeriodicComplex_homology_false_iso
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) :
    (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false ≅
      ModuleCat.of R (periodicHomology φ ψ hψφ) :=
  (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homologyIsoSc' true false true
      (PeriodicComplex.BundleCycles.periodicComplexShape.prev_eq' PeriodicComplex.BundleCycles.periodicComplexShape_true_false)
      (PeriodicComplex.BundleCycles.periodicComplexShape.next_eq' PeriodicComplex.BundleCycles.periodicComplexShape_false_true) ≪≫
    (ShortComplex.moduleCatMk ψ φ hψφ).moduleCatHomologyIso

def endomorphismPeriodicComplex_homology_true_iso
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) :
    (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true ≅
      ModuleCat.of R (periodicHomology ψ φ hφψ) :=
  (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homologyIsoSc' false true false
      (PeriodicComplex.BundleCycles.periodicComplexShape.prev_eq' PeriodicComplex.BundleCycles.periodicComplexShape_false_true)
      (PeriodicComplex.BundleCycles.periodicComplexShape.next_eq' PeriodicComplex.BundleCycles.periodicComplexShape_true_false) ≪≫
    (ShortComplex.moduleCatMk φ ψ hφψ).moduleCatHomologyIso

theorem periodicHomology_length_ne_top
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0)
    (hM : Module.length R M ≠ ⊤) :
    Module.length R (periodicHomology φ ψ hψφ) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ne_top_of_le_ne_top hM (Module.length_le_of_injective φ.ker.subtype
      φ.ker.subtype_injective))
    (Module.length_le_of_surjective (periodicBoundaryMap φ ψ hψφ).range.mkQ
      (Submodule.mkQ_surjective _))

end

/-!
# LineBundleCycles: exact periodic complexes have zero homology length
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodicBoundaryMap_surjective_of_exact
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) (hex : Function.Exact ψ φ) :
    Function.Surjective (periodicBoundaryMap φ ψ hψφ) := by
  intro x
  obtain ⟨y, hy⟩ := (hex x.1).mp x.2
  exact ⟨y, Subtype.ext hy⟩

theorem periodicHomology_length_zero_of_exact
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) (hex : Function.Exact ψ φ) :
    Module.length R (periodicHomology φ ψ hψφ) = 0 := by
  change Module.length R (φ.ker ⧸ (periodicBoundaryMap φ ψ hψφ).range) = 0
  rw [LinearMap.range_eq_top.mpr (periodicBoundaryMap_surjective_of_exact φ ψ hψφ hex)]
  exact Module.length_eq_zero

theorem endomorphismPeriodicComplex_homology_length_zero_of_exact
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hexφψ : Function.Exact φ ψ) (hexψφ : Function.Exact ψ φ) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology i) = 0 := by
  cases i
  · rw [(endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact periodicHomology_length_zero_of_exact φ ψ hψφ hexψφ
  · rw [(endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact periodicHomology_length_zero_of_exact ψ φ hφψ hexφψ

theorem endomorphismPeriodicEulerLength_zero_of_exact
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hexφψ : Function.Exact φ ψ) (hexψφ : Function.Exact ψ φ)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ = 0 := by
  unfold PeriodicComplex.BundleCycles.periodicEulerLength
  rw [endomorphismPeriodicComplex_homology_length_zero_of_exact φ ψ hφψ hψφ hexφψ hexψφ false,
    endomorphismPeriodicComplex_homology_length_zero_of_exact φ ψ hφψ hψφ hexφψ hexψφ true]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact.BundleCycles
