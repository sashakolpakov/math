import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductHomology
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorEuler
import Mathlib.Data.ENat.BigOperators

/-! # Product Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: periodic homology and Euler lengths of a finite product
-/

variable {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem periodicPiHomology_length (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0) :
    Module.length R (Exact.BundleCycles.periodicHomology (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ h)) =
      ∑ i, Module.length R (Exact.BundleCycles.periodicHomology (φ i) (ψ i) (h i)) := by
  rw [(ProductHomology.BundleCycles.periodicPiHomologyEquiv φ ψ h).length_eq, Module.length_pi_of_fintype]

theorem periodicPiHomology_length_ne_top (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0)
    (hf : ∀ i, Module.length R (Exact.BundleCycles.periodicHomology (φ i) (ψ i) (h i)) ≠ ⊤) :
    Module.length R (Exact.BundleCycles.periodicHomology (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ h)) ≠ ⊤ := by
  rw [periodicPiHomology_length φ ψ h]
  exact ENat.sum_ne_top.mpr (fun i _ => hf i)

theorem periodicPiHomology_length_toNat (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0)
    (hf : ∀ i, Module.length R (Exact.BundleCycles.periodicHomology (φ i) (ψ i) (h i)) ≠ ⊤) :
    (Module.length R (Exact.BundleCycles.periodicHomology (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ h))).toNat =
      ∑ i, (Module.length R (Exact.BundleCycles.periodicHomology (φ i) (ψ i) (h i))).toNat := by
  rw [periodicPiHomology_length φ ψ h]
  exact ENat.toNat_sum (fun i _ => hf i)

theorem periodicPiComplex_homology_finite (φ ψ : ∀ i, M i →ₗ[R] M i)
    (hφψ : ∀ i, (ψ i).comp (φ i) = 0) (hψφ : ∀ i, (φ i).comp (ψ i) = 0)
    (hf : ∀ (i : ι) (j : Bool), Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (φ i) (ψ i)
      (hφψ i) (hψφ i)).homology j) ≠ ⊤) (j : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero ψ φ hφψ) (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ hψφ)).homology j) ≠ ⊤ := by
  cases j
  · rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso _ _ _ _).toLinearEquiv.length_eq]
    apply periodicPiHomology_length_ne_top φ ψ hψφ
    intro i
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso (φ i) (ψ i)
      (hφψ i) (hψφ i)).toLinearEquiv.length_eq]
    exact hf i false
  · rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso _ _ _ _).toLinearEquiv.length_eq]
    apply periodicPiHomology_length_ne_top ψ φ hφψ
    intro i
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso (φ i) (ψ i)
      (hφψ i) (hψφ i)).toLinearEquiv.length_eq]
    exact hf i true

theorem periodicPiEulerLength_sum (φ ψ : ∀ i, M i →ₗ[R] M i)
    (hφψ : ∀ i, (ψ i).comp (φ i) = 0) (hψφ : ∀ i, (φ i).comp (ψ i) = 0)
    (hf₀ : ∀ i, Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (φ i) (ψ i)
      (hφψ i) (hψφ i)).homology false) ≠ ⊤)
    (hf₁ : ∀ i, Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (φ i) (ψ i)
      (hφψ i) (hψφ i)).homology true) ≠ ⊤)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero ψ φ hφψ) (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ hψφ)).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero ψ φ hφψ) (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ hψφ)).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (ProductHomology.BundleCycles.periodicPi_comp_zero ψ φ hφψ) (ProductHomology.BundleCycles.periodicPi_comp_zero φ ψ hψφ)) h₀ h₁ =
      ∑ i, PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (φ i) (ψ i)
        (hφψ i) (hψφ i)) (hf₀ i) (hf₁ i) := by
  have hH₀ (i : ι) : Module.length R (Exact.BundleCycles.periodicHomology (φ i) (ψ i) (hψφ i)) ≠ ⊤ := by
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso (φ i) (ψ i)
      (hφψ i) (hψφ i)).toLinearEquiv.length_eq]
    exact hf₀ i
  have hH₁ (i : ι) : Module.length R (Exact.BundleCycles.periodicHomology (ψ i) (φ i) (hφψ i)) ≠ ⊤ := by
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso (φ i) (ψ i)
      (hφψ i) (hψφ i)).toLinearEquiv.length_eq]
    exact hf₁ i
  simp only [ScalingOf.BundleCycles.periodicEulerLength_eq_homology_lengths]
  rw [periodicPiHomology_length_toNat φ ψ hψφ hH₀,
    periodicPiHomology_length_toNat ψ φ hφψ hH₁,
    Nat.cast_sum, Nat.cast_sum, Finset.sum_sub_distrib]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductLength.BundleCycles
