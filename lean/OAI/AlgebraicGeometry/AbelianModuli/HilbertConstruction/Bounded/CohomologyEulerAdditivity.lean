import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyDimensionBalance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Cohomology Euler Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CohomologyEulerAdditivity

noncomputable section

/-! Euler characteristic is additive for short exact sheaf sequences with finite-dimensional bounded cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem coefficientEulerCharacteristic_shortExact_of_bounded
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hfin₁ : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₁)
    (hfin₂ : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₂)
    (hfin₃ : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₃)
    (N : ℕ)
    (hz₁ : ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₁))
    (hz₂ : ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₂))
    (hz₃ : ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₃)) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₂ =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₁ + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₃ := by
  let a (q : ℕ) : ℤ := Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₁)
  let b (q : ℕ) : ℤ := Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₂)
  let c (q : ℕ) : ℤ := Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj S.X₃)
  let r (q : ℕ) : ℤ := Module.finrank K (LinearMap.range (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS q).hom)
  have hzero : a 0 - b 0 + c 0 = 0 + r 0 := by
    have := hfin₂ 0
    have := hfin₃ 0
    have hd := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_zero (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS
    dsimp only [a, b, c, r]
    omega
  have hsucc (q : ℕ) : a (q + 1) - b (q + 1) + c (q + 1) = 0 + r q + r (q + 1) := by
    have := hfin₁ (q + 1)
    have := hfin₂ (q + 1)
    have := hfin₃ (q + 1)
    have hd := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_succ (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS q
    dsimp only [a, b, c, r]
    omega
  have hr : r N = 0 := by
    have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (N + 1)).obj S.X₁) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz₁ (N + 1) (by omega))
    dsimp only [r]
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  have ht := AlternatingConeSums.alternating_dimension_telescope (fun q => a q - b q + c q) (fun _ => 0) r hzero hsucc N
  simp only [hr, mul_zero, Finset.sum_const_zero, zero_add] at ht
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at ht
  rw [CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sum p S.X₂ (N + 1) (fun q hq => hz₂ q (by omega)),
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sum p S.X₁ (N + 1) (fun q hq => hz₁ q (by omega)),
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sum p S.X₃ (N + 1) (fun q hq => hz₃ q (by omega))]
  change (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * b q) =
    (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * a q) +
      (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * c q)
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CohomologyEulerAdditivity
