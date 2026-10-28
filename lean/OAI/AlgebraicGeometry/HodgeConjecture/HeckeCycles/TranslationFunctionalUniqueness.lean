import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Schur

/-! # Translation Functional Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslationFunctionalUniqueness.CM

noncomputable section

/-! Translation-invariant functionals on the actual finite Schwartz
space are fixed by one lattice normalization. The proof uses the genuine
finite coset expansions and a common integer period. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeEigenline.CM

variable {I : Type*} [Fintype I]
  (J K : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] ℂ)
  (hJ : ∀ (q : ℚ) (hq : q ≠ 0) a, J (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) = J (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq))
  (hK : ∀ (q : ℚ) (hq : q ≠ 0) a, K (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) = K (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq))

include hJ hK in
theorem proportional_periodic (q : ℚ) (hq : q ≠ 0) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hp : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq, ∀ x, φ.val (u + x) = φ.val x) :
    K (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) * J φ = J (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) * K φ := by
  obtain ⟨s, hs⟩ := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_coset_expansion φ q hq hp
  let a : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := I) q hq → I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := fun c => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c)
  have hφ : φ = ∑ c ∈ s, φ.val (a c) • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (a c) := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply] using hs x
  conv_lhs => rw [hφ]
  conv_rhs => rw [hφ]
  simp only [map_sum, map_smul, smul_eq_mul, hJ, hK, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

include hJ hK in
theorem unique (h0 : J RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = K RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)
    (hk0 : K RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction ≠ 0)
    (hkn : ∀ (n : ℕ) (hn : 0 < n),
      K (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (n : ℚ) (by exact_mod_cast hn.ne')) ≠ 0) : J = K := by
  apply LinearMap.ext
  intro φ
  obtain ⟨n, hn, hp⟩ := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_lattice_period φ
  let hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have href : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n : ℚ) hq, ∀ x,
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (ι := I)).val (u + x) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction.val x := by
    intro u hu x
    exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_add (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral n hn hu) x
  have hv := proportional_periodic J K hJ hK (n : ℚ) hq RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction href
  rw [h0] at hv
  have hl : K (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (n : ℚ) hq) = J (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (n : ℚ) hq) :=
    mul_right_cancel₀ hk0 hv
  have hφ := proportional_periodic J K hJ hK (n : ℚ) hq φ hp
  rw [← hl] at hφ
  exact mul_left_cancel₀ (hkn n hn) hφ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslationFunctionalUniqueness.CM
