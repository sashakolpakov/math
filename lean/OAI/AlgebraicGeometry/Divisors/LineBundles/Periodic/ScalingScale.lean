import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingOf
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorEuler

/-! # Scaling Scale -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingScale.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: finiteness under scaling a periodic differential

Extended module length is additive in the actual nested quotient
sequence. Thus finite original homology and finite multiplication
cokernel on the differential image imply finite scaled homology.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem moduleLength_nestedQuotient (P Q : Submodule R M) (hPQ : P ≤ Q) :
    Module.length R (M ⧸ P) = Module.length R (Q ⧸ P.comap Q.subtype) + Module.length R (M ⧸ Q) := by
  have h := Module.length_eq_add_of_exact (Q.map P.mkQ).subtype (Q.map P.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  rw [← (SubquotientImage.BundleCycles.subquotientImageEquiv P Q).length_eq,
    (Submodule.quotientQuotientEquivQuotient P Q hPQ).length_eq] at h
  exact h

theorem periodicHomology_scaledIncoming_length_eq (x : R) (φ ψ : M →ₗ[R] M)
    (hψφ : φ.comp ψ = 0) :
    Module.length R (Exact.BundleCycles.periodicHomology φ (x • ψ) (ScalingOf.BundleCycles.periodic_smul_comp_zero x ψ φ hψφ)) =
      Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x ψ.range) + Module.length R (Exact.BundleCycles.periodicHomology φ ψ hψφ) := by
  change Module.length R (φ.ker ⧸ (Exact.BundleCycles.periodicBoundaryMap φ (x • ψ) _).range) = _
  rw [ScalingOf.BundleCycles.periodicBoundaryMap_scaledIncoming x φ ψ hψφ]
  have he := moduleLength_nestedQuotient (x • Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range
    (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range (NestedQuotientLength.BundleCycles.scaledRange_le x (Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ))
  rw [NestedQuotientLength.BundleCycles.scaledRange_comap_rangeSubtype,
    (EquationEulerEquiv.BundleCycles.equationCokernelEquiv x (ScalingOf.BundleCycles.periodicBoundaryRangeEquiv φ ψ hψφ)).length_eq] at he
  exact he

theorem periodicScaleLeft_homology_finite (x : R) (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range) ≠ ⊤) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (x • φ) ψ
      (ScalingOf.BundleCycles.periodic_smul_comp_zero x φ ψ hφψ) (ScalingOf.BundleCycles.periodic_comp_smul_zero x φ ψ hψφ)).homology i) ≠ ⊤ := by
  cases i
  · rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso _ _ _ _).toLinearEquiv.length_eq,
      (ScalingOf.BundleCycles.periodicHomology_scaledOutgoingEquiv x φ ψ hψφ hx).length_eq,
      ← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact h₀
  · rw [(Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso _ _ _ _).toLinearEquiv.length_eq,
      periodicHomology_scaledIncoming_length_eq x ψ φ hφψ,
      ← (Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso φ ψ hφψ hψφ).toLinearEquiv.length_eq]
    exact (ENat.add_lt_top.mpr ⟨hC.lt_top, h₁.lt_top⟩).ne

theorem periodicScaleRight_homology_finite (x : R) (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x ψ.range) ≠ ⊤) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ (x • ψ)
      (ScalingOf.BundleCycles.periodic_comp_smul_zero x ψ φ hφψ) (ScalingOf.BundleCycles.periodic_smul_comp_zero x ψ φ hψφ)).homology i) ≠ ⊤ := by
  have hswap₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ).homology false) ≠ ⊤ :=
    fun ht => h₁ ((FactorEuler.BundleCycles.endomorphismPeriodicHomology_swap_length φ ψ hφψ hψφ false).symm.trans ht)
  have hswap₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex ψ φ hψφ hφψ).homology true) ≠ ⊤ :=
    fun ht => h₀ ((FactorEuler.BundleCycles.endomorphismPeriodicHomology_swap_length φ ψ hφψ hψφ true).symm.trans ht)
  have hf := periodicScaleLeft_homology_finite x ψ φ hψφ hφψ hx hswap₀ hswap₁ hC (!i)
  have he := FactorEuler.BundleCycles.endomorphismPeriodicHomology_swap_length (x • ψ) φ
    (ScalingOf.BundleCycles.periodic_smul_comp_zero x ψ φ hψφ) (ScalingOf.BundleCycles.periodic_comp_smul_zero x ψ φ hφψ) i
  exact fun ht => hf (he.symm.trans ht)

end

section

/-!
# LineBundleCycles: scaling both actual periodic differentials

The two single-scaling calculations combine without changing the
second differential's image in the intermediate step.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodicDoubleScale_comp_zero (x y : R) (φ ψ : M →ₗ[R] M) (h : φ.comp ψ = 0) :
    (x • φ).comp (y • ψ) = 0 := by
  rw [LinearMap.smul_comp, LinearMap.comp_smul, h, smul_zero, smul_zero]

def periodicDoubleScaleComplex (x y : R) (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) :
    HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape :=
  PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (x • φ) (y • ψ)
    (periodicDoubleScale_comp_zero y x ψ φ hφψ) (periodicDoubleScale_comp_zero x y φ ψ hψφ)

theorem periodicDoubleScale_homology_finite (x y : R) (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (hy : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism y M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (hCx : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range) ≠ ⊤)
    (hCy : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel y ψ.range) ≠ ⊤) (i : Bool) :
    Module.length R ((periodicDoubleScaleComplex x y φ ψ hφψ hψφ).homology i) ≠ ⊤ :=
  periodicScaleRight_homology_finite y (x • φ) ψ
    (ScalingOf.BundleCycles.periodic_smul_comp_zero x φ ψ hφψ) (ScalingOf.BundleCycles.periodic_comp_smul_zero x φ ψ hψφ) hy
    (periodicScaleLeft_homology_finite x φ ψ hφψ hψφ hx h₀ h₁ hCx false)
    (periodicScaleLeft_homology_finite x φ ψ hφψ hψφ hx h₀ h₁ hCx true) hCy i

theorem periodicEulerLength_doubleScale (x y : R) (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (hy : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism y M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (hKx : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x φ.range) ≠ ⊤)
    (hCx : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range) ≠ ⊤)
    (hKy : Module.length R (MultiplicationSequence.BundleCycles.equationKernel y ψ.range) ≠ ⊤)
    (hCy : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel y ψ.range) ≠ ⊤)
    (hD₀ : Module.length R ((periodicDoubleScaleComplex x y φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (hD₁ : Module.length R ((periodicDoubleScaleComplex x y φ ψ hφψ hψφ).homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (periodicDoubleScaleComplex x y φ ψ hφψ hψφ) hD₀ hD₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ -
        EquationEulerLength.BundleCycles.equationEulerLength x φ.range hKx hCx + EquationEulerLength.BundleCycles.equationEulerLength y ψ.range hKy hCy := by
  let hL₀ := periodicScaleLeft_homology_finite x φ ψ hφψ hψφ hx h₀ h₁ hCx false
  let hL₁ := periodicScaleLeft_homology_finite x φ ψ hφψ hψφ hx h₀ h₁ hCx true
  have hleft := ScalingOf.BundleCycles.periodicEulerLength_scaleLeft_of_injective x φ ψ hφψ hψφ hx h₀ h₁ hL₀ hL₁ hKx hCx
  have hright := ScalingOf.BundleCycles.periodicEulerLength_scaleRight_of_injective y (x • φ) ψ
    (ScalingOf.BundleCycles.periodic_smul_comp_zero x φ ψ hφψ) (ScalingOf.BundleCycles.periodic_comp_smul_zero x φ ψ hψφ) hy
    hL₀ hL₁ hD₀ hD₁ hKy hCy
  exact hright.trans (congrArg (fun z => z + EquationEulerLength.BundleCycles.equationEulerLength y ψ.range hKy hCy) hleft)

theorem periodicEulerLength_endomorphisms_congr
    (φ ψ φ' ψ' : M →ₗ[R] M) (hφ : φ = φ') (hψ : ψ = ψ')
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hφψ' : ψ'.comp φ' = 0) (hψφ' : φ'.comp ψ' = 0)
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (h₀' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ').homology false) ≠ ⊤)
    (h₁' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ').homology true) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ') h₀' h₁' := by
  subst φ'
  subst ψ'
  rfl

end

/-!
# LineBundleCycles: Euler comparison from equal scaled differentials

This combines the two proved scaling identities. All homology and
equation finiteness hypotheses concern actual modules; finiteness of
the common scaled complex is derived in the proof.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem periodicEulerLength_factorized (x y u v : R) (φ ψ φ' ψ' : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0)
    (hφψ' : ψ'.comp φ' = 0) (hψφ' : φ'.comp ψ' = 0)
    (heφ : x • φ = u • φ') (heψ : y • ψ = v • ψ')
    (hx : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x M))
    (hy : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism y M))
    (hu : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism u M))
    (hv : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism v M))
    (h₀ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology false) ≠ ⊤)
    (h₁ : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ).homology true) ≠ ⊤)
    (h₀' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ').homology false) ≠ ⊤)
    (h₁' : Module.length R ((PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ').homology true) ≠ ⊤)
    (hKx : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x φ.range) ≠ ⊤)
    (hCx : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x φ.range) ≠ ⊤)
    (hKy : Module.length R (MultiplicationSequence.BundleCycles.equationKernel y ψ.range) ≠ ⊤)
    (hCy : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel y ψ.range) ≠ ⊤)
    (hKu : Module.length R (MultiplicationSequence.BundleCycles.equationKernel u φ'.range) ≠ ⊤)
    (hCu : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel u φ'.range) ≠ ⊤)
    (hKv : Module.length R (MultiplicationSequence.BundleCycles.equationKernel v ψ'.range) ≠ ⊤)
    (hCv : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel v ψ'.range) ≠ ⊤) :
    PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ ψ hφψ hψφ) h₀ h₁ =
      PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.endomorphismPeriodicComplex φ' ψ' hφψ' hψφ') h₀' h₁' +
        EquationEulerLength.BundleCycles.equationEulerLength x φ.range hKx hCx - EquationEulerLength.BundleCycles.equationEulerLength y ψ.range hKy hCy -
        EquationEulerLength.BundleCycles.equationEulerLength u φ'.range hKu hCu + EquationEulerLength.BundleCycles.equationEulerLength v ψ'.range hKv hCv := by
  let hD₀ := periodicDoubleScale_homology_finite x y φ ψ hφψ hψφ hx hy h₀ h₁ hCx hCy false
  let hD₁ := periodicDoubleScale_homology_finite x y φ ψ hφψ hψφ hx hy h₀ h₁ hCx hCy true
  let hD₀' := periodicDoubleScale_homology_finite u v φ' ψ' hφψ' hψφ' hu hv h₀' h₁' hCu hCv false
  let hD₁' := periodicDoubleScale_homology_finite u v φ' ψ' hφψ' hψφ' hu hv h₀' h₁' hCu hCv true
  have he := periodicEulerLength_endomorphisms_congr (x • φ) (y • ψ) (u • φ') (v • ψ') heφ heψ
    (periodicDoubleScale_comp_zero y x ψ φ hφψ) (periodicDoubleScale_comp_zero x y φ ψ hψφ)
    (periodicDoubleScale_comp_zero v u ψ' φ' hφψ') (periodicDoubleScale_comp_zero u v φ' ψ' hψφ')
    hD₀ hD₁ hD₀' hD₁'
  have hleft := periodicEulerLength_doubleScale x y φ ψ hφψ hψφ hx hy h₀ h₁ hKx hCx hKy hCy hD₀ hD₁
  have hright := periodicEulerLength_doubleScale u v φ' ψ' hφψ' hψφ' hu hv h₀' h₁' hKu hCu hKv hCv hD₀' hD₁'
  have hcomparison := hleft.symm.trans (he.trans hright)
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingScale.BundleCycles
