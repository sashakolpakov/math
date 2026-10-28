import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact

/-! # Finite Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite modules have zero periodic Euler length

The two kernel-image sequences and the two homology quotient sequences
cancel. No exactness of the periodic complex is required.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodicBoundaryMap_kernel_exact
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) :
    Function.Exact ψ.ker.subtype (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).rangeRestrict := by
  intro x
  constructor
  · intro hx
    have hz : ψ x = 0 := congrArg
      (fun z : (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range => (z.1 : M)) hx
    exact ⟨⟨x, hz⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (Subtype.ext x.2)

theorem periodicHomology_length_eq_of_finite
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hM : Module.length R M ≠ ⊤) :
    (Module.length R (Periodic.Exact.BundleCycles.periodicHomology φ ψ hψφ)).toNat =
      (Module.length R (Periodic.Exact.BundleCycles.periodicHomology ψ φ hφψ)).toNat := by
  have hKφ : Module.length R φ.ker ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective φ.ker.subtype
      φ.ker.subtype_injective)
  have hKψ : Module.length R ψ.ker ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective ψ.ker.subtype
      ψ.ker.subtype_injective)
  have h₁ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact ψ.ker.subtype
    (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).rangeRestrict ψ.ker.subtype_injective
    (LinearMap.surjective_rangeRestrict _) (periodicBoundaryMap_kernel_exact φ ψ hψφ) hM
  have h₂ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact φ.ker.subtype
    (Periodic.Exact.BundleCycles.periodicBoundaryMap ψ φ hφψ).rangeRestrict φ.ker.subtype_injective
    (LinearMap.surjective_rangeRestrict _) (periodicBoundaryMap_kernel_exact ψ φ hφψ) hM
  have h₃ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range.subtype
    (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range.mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _) hKφ
  have h₄ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact (Periodic.Exact.BundleCycles.periodicBoundaryMap ψ φ hφψ).range.subtype
    (Periodic.Exact.BundleCycles.periodicBoundaryMap ψ φ hφψ).range.mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _) hKψ
  change (Module.length R (φ.ker ⧸ (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range)).toNat =
    (Module.length R (ψ.ker ⧸ (Periodic.Exact.BundleCycles.periodicBoundaryMap ψ φ hφψ).range)).toNat
  omega

theorem endomorphismPeriodicComplex_homology_length_ne_top
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hM : Module.length R M ≠ ⊤) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology i) ≠ ⊤ := by
  cases i
  · rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact Periodic.Exact.BundleCycles.periodicHomology_length_ne_top φ ψ hψφ hM
  · rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact Periodic.Exact.BundleCycles.periodicHomology_length_ne_top ψ φ hφψ hM

theorem endomorphismPeriodicEulerLength_zero_of_finite
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (hM : Module.length R M ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ = 0 := by
  unfold PeriodicComplex.BundleCycles.periodicEulerLength
  rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq,
    (Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
  exact sub_eq_zero.mpr (congrArg (fun n : ℕ => (n : ℤ))
    (periodicHomology_length_eq_of_finite φ ψ hφψ hψφ hM))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteLength.BundleCycles
