import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact
import OAI.AlgebraicGeometry.Divisors.LineBundles.NestedQuotientLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv

/-! # Scaling Of -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingOf.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: homology comparisons when a differential is scaled

An injective scalar leaves the outgoing kernel unchanged. For the other
homology module, its image shrinks by precisely that scalar. All maps
below come from the actual kernel inclusions and image representatives.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodic_smul_comp_zero (x : R) (φ ψ : M →ₗ[R] M) (h : ψ.comp φ = 0) :
    ψ.comp (x • φ) = 0 := by
  rw [LinearMap.comp_smul, h, smul_zero]

theorem periodic_comp_smul_zero (x : R) (φ ψ : M →ₗ[R] M) (h : φ.comp ψ = 0) :
    (x • φ).comp ψ = 0 := by
  rw [LinearMap.smul_comp, h, smul_zero]

theorem periodic_smul_kernel (x : R) (φ : M →ₗ[R] M)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M)) : (x • φ).ker = φ.ker := by
  ext m
  constructor
  · intro hm
    apply hx
    exact hm.trans (map_zero (MultiplicationSequence.BundleCycles.equationEndomorphism x M)).symm
  · intro hm
    change x • φ m = 0
    rw [show φ m = 0 from hm, smul_zero]

def periodicHomology_scaledOutgoingEquiv (x : R) (φ ψ : M →ₗ[R] M)
    (hψφ : φ.comp ψ = 0) (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M)) :
    Exact.BundleCycles.periodicHomology (x • φ) ψ (periodic_comp_smul_zero x φ ψ hψφ) ≃ₗ[R]
      Exact.BundleCycles.periodicHomology φ ψ hψφ :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (periodic_smul_kernel x φ hx)) (by
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, Subtype.ext rfl⟩
    · rintro ⟨n, rfl⟩
      refine ⟨Exact.BundleCycles.periodicBoundaryMap (x • φ) ψ (periodic_comp_smul_zero x φ ψ hψφ) n,
        ⟨n, rfl⟩, ?_⟩
      exact Subtype.ext rfl)

theorem periodicBoundaryMap_scaledIncoming (x : R) (φ ψ : M →ₗ[R] M)
    (hψφ : φ.comp ψ = 0) :
    Exact.BundleCycles.periodicBoundaryMap φ (x • ψ) (periodic_smul_comp_zero x ψ φ hψφ) =
      x • Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ := by
  ext m
  rfl

def periodicBoundaryRangeEquiv (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0) :
    (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range ≃ₗ[R] ψ.range := by
  let f : (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range →ₗ[R] ψ.range :=
    LinearMap.codRestrict ψ.range
      (φ.ker.subtype.comp (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range.subtype) (fun m => by
        obtain ⟨n, hn⟩ := m.2
        exact ⟨n, congrArg Subtype.val hn⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro m n h
    have hv : (m.1 : M) = (n.1 : M) :=
      congrArg (fun z : ψ.range => (z : M)) h
    exact Subtype.ext (Subtype.ext hv)
  · intro m
    obtain ⟨n, hn⟩ := m.2
    exact ⟨⟨Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ n, ⟨n, rfl⟩⟩, Subtype.ext hn⟩

theorem periodicHomology_scaledIncoming_length (x : R) (φ ψ : M →ₗ[R] M)
    (hψφ : φ.comp ψ = 0)
    (h : Module.length R (Exact.BundleCycles.periodicHomology φ (x • ψ)
      (periodic_smul_comp_zero x ψ φ hψφ)) ≠ ⊤) :
    (Module.length R (Exact.BundleCycles.periodicHomology φ (x • ψ)
      (periodic_smul_comp_zero x ψ φ hψφ))).toNat =
      (Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x ψ.range)).toNat +
      (Module.length R (Exact.BundleCycles.periodicHomology φ ψ hψφ)).toNat := by
  change Module.length R (φ.ker ⧸ (Exact.BundleCycles.periodicBoundaryMap φ (x • ψ) _).range) ≠ ⊤ at h
  rw [periodicBoundaryMap_scaledIncoming x φ ψ hψφ] at h
  have he := NestedQuotientLength.BundleCycles.moduleLengthNat_scaledRangeQuotient x (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ) h
  rw [(EquationEulerEquiv.BundleCycles.equationCokernelEquiv x (periodicBoundaryRangeEquiv φ ψ hψφ)).length_eq] at he
  change (Module.length R (φ.ker ⧸ (Exact.BundleCycles.periodicBoundaryMap φ (x • ψ) _).range)).toNat = _
  rw [periodicBoundaryMap_scaledIncoming x φ ψ hψφ]
  exact he

end

section

/-!
# LineBundleCycles: periodic Euler length under an injective scalar

Scaling the first differential subtracts the one-equation Euler length
on its actual image. The proof uses unchanged outgoing homology and
the nested image quotient for incoming homology.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem equationKernel_range_length_zero (x : R) (φ : M →ₗ[R] M)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M)) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel x φ.range) = 0 := by
  have hi : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x φ.range) := by
    intro m n h
    apply Subtype.ext
    apply hx
    exact congrArg (fun z : φ.range => (z : M)) h
  rw [MultiplicationSequence.BundleCycles.equationKernel, LinearMap.ker_eq_bot.mpr hi, Module.length_bot]

theorem periodicEulerLength_scaleLeft_of_injective
    (x : R) (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (h₀' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)).homology false) ≠ ⊤)
    (h₁' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)).homology true) ≠ ⊤)
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x φ.range) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)) h₀' h₁' =
      PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ -
        EquationEulerLength.BundleCycles.equationEulerLength x φ.range hK hC := by
  have hs : Module.length R (Exact.BundleCycles.periodicHomology ψ (x • φ)
      (periodic_smul_comp_zero x φ ψ hφψ)) ≠ ⊤ := by
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)).toLinearEquiv.length_eq]
    exact h₁'
  have he := periodicHomology_scaledIncoming_length x ψ φ hφψ hs
  have hk := equationKernel_range_length_zero x φ hx
  unfold PeriodicComplex.BundleCycles.periodicEulerLength EquationEulerLength.BundleCycles.equationEulerLength
  rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)).toLinearEquiv.length_eq,
    (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso (x • φ) ψ
      (periodic_smul_comp_zero x φ ψ hφψ)
      (periodic_comp_smul_zero x φ ψ hψφ)).toLinearEquiv.length_eq,
    (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq,
    (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq,
    (periodicHomology_scaledOutgoingEquiv x φ ψ hψφ hx).length_eq,
    hk, ENat.toNat_zero]
  change ((Module.length R (Exact.BundleCycles.periodicHomology φ ψ hψφ)).toNat : ℤ) -
      (Module.length R (Exact.BundleCycles.periodicHomology ψ (x • φ)
        (periodic_smul_comp_zero x φ ψ hφψ))).toNat =
    ((Module.length R (Exact.BundleCycles.periodicHomology φ ψ hψφ)).toNat : ℤ) -
      (Module.length R (Exact.BundleCycles.periodicHomology ψ φ hφψ)).toNat -
      ((Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range)).toNat - 0)
  omega

end

/-!
# LineBundleCycles: explicit periodic Euler length and interchange of the differentials
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodicEulerLength_eq_homology_lengths
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ =
      ((Module.length R (Exact.BundleCycles.periodicHomology φ ψ hψφ)).toNat : ℤ) -
        (Module.length R (Exact.BundleCycles.periodicHomology ψ φ hφψ)).toNat := by
  unfold PeriodicComplex.BundleCycles.periodicEulerLength
  rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq,
    (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]

theorem periodicEulerLength_swap
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (h₀' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ).homology false) ≠ ⊤)
    (h₁' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ) h₀' h₁' =
      -PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ := by
  rw [periodicEulerLength_eq_homology_lengths, periodicEulerLength_eq_homology_lengths]
  omega

theorem periodicEulerLength_scaleRight_of_injective
    (x : R) (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (h₀' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ (x • ψ)
      (periodic_comp_smul_zero x ψ φ hφψ)
      (periodic_smul_comp_zero x ψ φ hψφ)).homology false) ≠ ⊤)
    (h₁' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ (x • ψ)
      (periodic_comp_smul_zero x ψ φ hφψ)
      (periodic_smul_comp_zero x ψ φ hψφ)).homology true) ≠ ⊤)
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x ψ.range) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x ψ.range) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ (x • ψ)
      (periodic_comp_smul_zero x ψ φ hφψ)
      (periodic_smul_comp_zero x ψ φ hψφ)) h₀' h₁' =
      PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ +
        EquationEulerLength.BundleCycles.equationEulerLength x ψ.range hK hC := by
  have hs : Module.length R (Exact.BundleCycles.periodicHomology φ (x • ψ)
      (periodic_smul_comp_zero x ψ φ hψφ)) ≠ ⊤ := by
    rw [← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ (x • ψ)
      (periodic_comp_smul_zero x ψ φ hφψ)
      (periodic_smul_comp_zero x ψ φ hψφ)).toLinearEquiv.length_eq]
    exact h₀'
  have he := periodicHomology_scaledIncoming_length x φ ψ hψφ hs
  rw [periodicEulerLength_eq_homology_lengths, periodicEulerLength_eq_homology_lengths,
    (periodicHomology_scaledOutgoingEquiv x ψ φ hφψ hx).length_eq]
  unfold EquationEulerLength.BundleCycles.equationEulerLength
  rw [equationKernel_range_length_zero x ψ hx, ENat.toNat_zero]
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingOf.BundleCycles
