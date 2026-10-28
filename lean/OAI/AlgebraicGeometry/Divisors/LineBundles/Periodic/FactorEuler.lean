import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorKill
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorSequence

/-! # Factor Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorEuler.BundleCycles

noncomputable section

/-!
# LineBundleCycles: composition of scalar factors in the periodic Euler invariant

The explicit cone sequence and its constructed homotopy equivalence
prove e(ab,c) = e(a,bc) + e(b,ac). All homology finiteness conditions
refer to the actual complexes.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem endomorphismPeriodicHomology_swap_length
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ).homology i) =
      Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology (!i)) := by
  cases i
  · rw [Bool.not_false,
      (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso ψ φ hψφ hφψ).toLinearEquiv.length_eq,
      (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
  · rw [Bool.not_true,
      (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso ψ φ hψφ hφψ).toLinearEquiv.length_eq,
      (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]

theorem equationPeriodicHomology_swap_length (a b : R) (h : ∀ m : M, (a * b) • m = 0)
    (i : Bool) :
    Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b a (EquationPeriodicComplex.BundleCycles.equationPeriodic_kill_swap a b h)).homology i) =
      Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology (!i)) :=
  endomorphismPeriodicHomology_swap_length _ _ _ _ i

theorem periodicEulerLength_factor_comp (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0)
    (hAB₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c h).homology false) ≠ ⊤)
    (hAB₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c h).homology true) ≠ ⊤)
    (hA₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a (b * c)
      (FactorKill.BundleCycles.factorCone_kill_source a b c h)).homology false) ≠ ⊤)
    (hA₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a (b * c)
      (FactorKill.BundleCycles.factorCone_kill_source a b c h)).homology true) ≠ ⊤)
    (hB₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c)
      (FactorKill.BundleCycles.factorCone_kill_middle a b c h)).homology false) ≠ ⊤)
    (hB₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c)
      (FactorKill.BundleCycles.factorCone_kill_middle a b c h)).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c h) hAB₀ hAB₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a (b * c)
        (FactorKill.BundleCycles.factorCone_kill_source a b c h)) hA₀ hA₁ +
      PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c)
        (FactorKill.BundleCycles.factorCone_kill_middle a b c h)) hB₀ hB₁ := by
  let hQ := EquationPeriodicComplex.BundleCycles.equationPeriodic_kill_swap a (b * c) (FactorKill.BundleCycles.factorCone_kill_source a b c h)
  have hQ₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (b * c) a hQ).homology false) ≠ ⊤ := by
    rw [equationPeriodicHomology_swap_length]
    exact hA₁
  have hQ₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (b * c) a hQ).homology true) ≠ ⊤ := by
    rw [equationPeriodicHomology_swap_length]
    exact hA₀
  have hC₀ : Module.length R ((FactorKill.BundleCycles.periodicFactorCone a b c h).homology false) ≠ ⊤ := by
    rw [(FactorKill.BundleCycles.factorConeHomologyIso a b c h false).toLinearEquiv.length_eq]
    exact hB₀
  have hC₁ : Module.length R ((FactorKill.BundleCycles.periodicFactorCone a b c h).homology true) ≠ ⊤ := by
    rw [(FactorKill.BundleCycles.factorConeHomologyIso a b c h true).toLinearEquiv.length_eq]
    exact hB₁
  have he := PeriodicComplex.BundleCycles.periodicEulerLength_additive (FactorSequence.BundleCycles.factorConeSequence a b c h)
    (FactorSequence.BundleCycles.factorConeSequence_shortExact a b c h) hAB₀ hAB₁ hC₀ hC₁ hQ₀ hQ₁
  have hswap := EquationPeriodicComplex.BundleCycles.equationPeriodicEulerLength_swap a (b * c)
    (FactorKill.BundleCycles.factorCone_kill_source a b c h) hA₀ hA₁ hQ₀ hQ₁
  have hc : PeriodicComplex.BundleCycles.periodicEulerLength (FactorKill.BundleCycles.periodicFactorCone a b c h) hC₀ hC₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c)
        (FactorKill.BundleCycles.factorCone_kill_middle a b c h)) hB₀ hB₁ := by
    unfold PeriodicComplex.BundleCycles.periodicEulerLength
    rw [(FactorKill.BundleCycles.factorConeHomologyIso a b c h false).toLinearEquiv.length_eq,
      (FactorKill.BundleCycles.factorConeHomologyIso a b c h true).toLinearEquiv.length_eq]
  change PeriodicComplex.BundleCycles.periodicEulerLength (FactorKill.BundleCycles.periodicFactorCone a b c h) hC₀ hC₁ =
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c h) hAB₀ hAB₁ +
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (b * c) a hQ) hQ₀ hQ₁ at he
  rw [hc, hswap] at he
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorEuler.BundleCycles
