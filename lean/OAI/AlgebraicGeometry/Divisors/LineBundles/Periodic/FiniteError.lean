import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicSequence
import OAI.AlgebraicGeometry.Divisors.LineBundles.ExactLengthFiniteness

/-! # Finite Error -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteError.BundleCycles

noncomputable section

/-!
# LineBundleCycles: periodic Euler invariance under finite kernel and cokernel

The two actual module sequences through the image of a map give the
comparison. Their finite error modules have zero periodic Euler length,
and the homology sequence supplies finiteness of the image homology.
-/

universe u v

variable {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem linearMap_kernel_range_exact (f : M →ₗ[R] N) :
    Function.Exact f.ker.subtype f.rangeRestrict := by
  intro m
  constructor
  · intro hm
    exact ⟨⟨m, congrArg (fun y : f.range => (y : N)) hm⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    exact Subtype.ext m.2

theorem equationPeriodicEulerLength_eq_of_finite_errors
    (a b : R) (hM : ∀ m : M, (a * b) • m = 0) (hN : ∀ m : N, (a * b) • m = 0)
    (f : M →ₗ[R] N) (hK : Module.length R f.ker ≠ ⊤)
    (hQ : Module.length R (N ⧸ f.range) ≠ ⊤)
    (hM₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM).homology false) ≠ ⊤)
    (hM₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM).homology true) ≠ ⊤)
    (hN₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hN).homology false) ≠ ⊤)
    (hN₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hN).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM) hM₀ hM₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hN) hN₀ hN₁ := by
  let hk := EquationPeriodicSequence.BundleCycles.equationPeriodic_kill_submodule a b hM f.ker
  let hr := EquationPeriodicSequence.BundleCycles.equationPeriodic_kill_submodule a b hN f.range
  let hq := EquationPeriodicSequence.BundleCycles.equationPeriodic_kill_quotient a b hN f.range
  let S := EquationPeriodicSequence.BundleCycles.equationPeriodicSequence a b hk hM hr f.ker.subtype f.rangeRestrict
    (linearMap_kernel_range_exact f).linearMap_comp_eq_zero
  have hS : S.ShortExact := EquationPeriodicSequence.BundleCycles.equationPeriodicSequence_shortExact a b hk hM hr
    f.ker.subtype f.rangeRestrict (linearMap_kernel_range_exact f)
    f.ker.subtype_injective f.surjective_rangeRestrict
  have hKH (i : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hk).homology i) ≠ ⊤ :=
    EquationPeriodicSequence.BundleCycles.equationPeriodic_homology_finite_of_module a b hk hK i
  have hMH (i : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM).homology i) ≠ ⊤ := by
    cases i
    · exact hM₀
    · exact hM₁
  have hRH (i : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hr).homology i) ≠ ⊤ :=
    ExactLengthFiniteness.BundleCycles.periodicShortExact_homology_finite_right S hS hKH hMH i
  let T := EquationPeriodicSequence.BundleCycles.equationPeriodicSequence a b hr hN hq f.range.subtype f.range.mkQ
    (LinearMap.exact_subtype_mkQ f.range).linearMap_comp_eq_zero
  have hT : T.ShortExact := EquationPeriodicSequence.BundleCycles.equationPeriodicSequence_shortExact a b hr hN hq
    f.range.subtype f.range.mkQ (LinearMap.exact_subtype_mkQ f.range)
    f.range.subtype_injective f.range.mkQ_surjective
  have hQH (i : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hq).homology i) ≠ ⊤ :=
    EquationPeriodicSequence.BundleCycles.equationPeriodic_homology_finite_of_module a b hq hQ i
  have heS := PeriodicComplex.BundleCycles.periodicEulerLength_additive S hS (hKH false) (hKH true)
    hM₀ hM₁ (hRH false) (hRH true)
  have heT := PeriodicComplex.BundleCycles.periodicEulerLength_additive T hT (hRH false) (hRH true)
    hN₀ hN₁ (hQH false) (hQH true)
  have hKzero := EquationPeriodicSequence.BundleCycles.equationPeriodicEuler_zero_of_module a b hk hK (hKH false) (hKH true)
  have hQzero := EquationPeriodicSequence.BundleCycles.equationPeriodicEuler_zero_of_module a b hq hQ (hQH false) (hQH true)
  change PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM) hM₀ hM₁ =
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hk) (hKH false) (hKH true) +
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hr) (hRH false) (hRH true) at heS
  change PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hN) hN₀ hN₁ =
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hr) (hRH false) (hRH true) +
    PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hq) (hQH false) (hQH true) at heT
  rw [hKzero, zero_add] at heS
  rw [hQzero, add_zero] at heT
  exact heS.trans heT.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteError.BundleCycles
