import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitTest
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Prime Unramified -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeUnramified.Local

noncomputable section

/-! Integral finite tests with prime-to-q translation level have one
unit-ball factor for the entire q-adic position space. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

local instance fullPrimePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def truthIndicator (P : Prop) : ℂ := @ite ℂ P (Classical.propDecidable P) 1 0

theorem positionReindex_asFunction {I J K : Type*} [TopologicalSpace K]
    (e : I ≃ J) (x : I → K) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x = (fun j => x (e.symm j)) := rfl

theorem indicator_factor_of_retraction {X : Type*} (f : X → ℂ) (r : X → X) (P : X → Prop)
    (hyes : ∀ x, P x → f x = f (r x)) (hno : ∀ x, ¬ P x → f x = 0) (x : X) :
    f x = truthIndicator (P x) * f (r x) := by
  by_cases h : P x
  · simpa only [truthIndicator, ite_eq_left h, one_mul] using hyes x h
  · simp only [truthIndicator, ite_eq_right h, zero_mul, hno x h]

variable (q : ℕ) [Fact q.Prime] {I : Type} [Fintype I]

omit [Fintype I] in
theorem fullPrimeInclusion_level (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (x : I → ℚ_[q]) (hx : ∀ i, ‖x i‖ ≤ 1) :
    RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne') := by
  apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff _ _ _).mpr
  have he : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (N : ℚ)⁻¹ (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q x) =
      RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q ((N : ℚ)⁻¹ • x) :=
    ((RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q).map_smul (N : ℚ)⁻¹ x).symm
  rw [he]
  intro i
  apply RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization.finitePadicInclusion_integral q
  have hn : ‖(N : ℚ_[q])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  simpa [Algebra.smul_def, norm_mul, hn] using hx i

theorem finite_test_full_prime_retraction
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hp : ∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1) :
    φ.val x = φ.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val :=
  (congrArg φ.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrime_decomposition q x).symm).trans
    (hperiod _ (fullPrimeInclusion_level q N hN hcop (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x) hp)
      (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val)

omit [Fintype I] in
theorem fullPrimeProjection_component (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (i : I) :
    RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (x i) := rfl

omit [Fintype I] in
theorem fullPrimeProjection_integral (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) :
    ∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1 := by
  intro i
  rw [fullPrimeProjection_component]
  exact RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_integral_norm q (x i) (hx i)

theorem finite_test_full_prime_zero
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : ¬ ∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1) : φ.val x = 0 :=
  hsupport x (fun hx => hp (fullPrimeProjection_integral q x hx))

theorem finite_test_full_prime_factor
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    φ.val x = truthIndicator (∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1) *
      φ.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val :=
  indicator_factor_of_retraction φ.val (fun x => (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val)
    (fun x => ∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1)
    (finite_test_full_prime_retraction q φ N hN hcop hperiod)
    (finite_test_full_prime_zero q φ hsupport) x

variable {n : ℕ} (e : I ≃ Fin n)

def indexedPrimeAwayTest (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) :=
  RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (0 : Fin n → ℚ_[q]) ((RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeChart q e)).symm φ)

theorem indexedPrimeAwayTest_apply (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (y : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) :
    (indexedPrimeAwayTest q e φ).val y = φ.val y.val := by
  change φ.val ((RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q).symm ((RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e).symm 0, y)) = φ.val y.val
  change φ.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q 0 + y.val) = φ.val y.val
  rw [map_zero, zero_add]

omit [Fintype I] in
theorem padicUnitIndicator_reindex (x : I → ℚ_[q]) :
    LocalUnitTest.padicUnitIndicator q n (fun j => x (e.symm j)) = truthIndicator (∀ i, ‖x i‖ ≤ 1) := by
  have hi : (∀ j, ‖x (e.symm j)‖ ≤ 1) ↔ ∀ i, ‖x i‖ ≤ 1 := by
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h j
      exact h (e.symm j)
  by_cases h : ∀ i, ‖x i‖ ≤ 1
  · rw [LocalUnitTest.padicUnitIndicator_of_integral q n _ (hi.mpr h)]
    simp only [truthIndicator, ite_eq_left h]
  · rw [LocalUnitTest.padicUnitIndicator_of_not_integral q n _ (fun hh => h (hi.mp hh))]
    simp only [truthIndicator, ite_eq_right h]

omit [Fintype I] in
theorem indexedPrimeProjection_asFunction (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x = (fun j => RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x (e.symm j)) :=
  positionReindex_asFunction e (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x)

omit [Fintype I] in
theorem indexedPrimeUnitIndicator (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    LocalUnitTest.padicUnitIndicator q n (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x) =
      truthIndicator (∀ i, ‖RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i‖ ≤ 1) :=
  (congrArg (LocalUnitTest.padicUnitIndicator q n) (indexedPrimeProjection_asFunction q e x)).trans
    (padicUnitIndicator_reindex q e (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x))

theorem finite_test_full_prime_tensor
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x) :
    φ = RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (LocalUnitTest.padicUnitTest q n) (indexedPrimeAwayTest q e φ) := by
  apply Subtype.ext
  funext x
  rw [RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor_apply, indexedPrimeAwayTest_apply]
  change φ.val x = LocalUnitTest.padicUnitIndicator q n (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x) * φ.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val
  rw [indexedPrimeUnitIndicator]
  exact finite_test_full_prime_factor q φ hsupport N hN hcop hperiod x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeUnramified.Local
