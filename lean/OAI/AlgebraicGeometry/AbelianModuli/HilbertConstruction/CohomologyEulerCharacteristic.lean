import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ComplexEulerFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero
import Mathlib.Algebra.BigOperators.Finprod

/-! # Cohomology Euler Characteristic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

noncomputable section

/-! Euler characteristic of genuine coefficient cohomology, with explicit finite-support and finite-model identities. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def coefficientEulerCharacteristic {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q *
    (Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) : ℤ)

theorem coefficientEulerCharacteristic_eq_sum {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) (N : ℕ)
    (hzero : ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M)) :
    coefficientEulerCharacteristic p M =
      ∑ q ∈ Finset.range N, (-1 : ℤ) ^ q *
        (Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
          (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) : ℤ) := by
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra hn
  have hN : N ≤ q := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hn
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := ModuleCat.isZero_iff_subsingleton.mp (hzero q hN)
  exact hq (by simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero])

theorem coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
    (hzero : ∀ q, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).obj M)) :
    coefficientEulerCharacteristic p M =
      (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) : ℤ) := by
  have hs : coefficientEulerCharacteristic p M =
      (Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0).obj M) : ℤ) := by
    unfold coefficientEulerCharacteristic
    rw [finsum_eq_single _ 0]
    · simp
    · intro q hq
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
      have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
          (Coefficient.ModulePresheaf.schemeCoefficientMap p) (j + 1)).obj M) :=
        ModuleCat.isZero_iff_subsingleton.mp (hzero j)
      simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]
  exact hs.trans (congrArg (fun n : ℕ => (n : ℤ))
    (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).finrank_eq)

theorem coefficientEulerCharacteristic_eq_finite_model
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
    (D : CochainComplex (ModuleCat.{u} K) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite K (D.X q)) (hbound : ∀ q, N ≤ q → IsZero (D.X q))
    (e : ∀ q, D.homology q ≅ (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) :
    coefficientEulerCharacteristic p M =
      ∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.X q) : ℤ) := by
  have hz : ∀ q, N + 1 ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := by
    intro q hq
    exact (e q).isZero_iff.mp (HomologicalComplex.ExactAt.of_isZero (hbound q (by omega))).isZero_homology
  rw [coefficientEulerCharacteristic_eq_sum p M (N + 1) hz,
    HilbertConstruction.Finite.ComplexEulerFormula.cochain_euler_sum_of_final_zero D hfinite N (hbound (N + 1) (by omega))]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (e q).toLinearEquiv.finrank_eq.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic
