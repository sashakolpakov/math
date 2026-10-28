import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlternatingConeSums
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.DimensionBalance

/-! # Complex Euler Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ComplexEulerFormula

noncomputable section

/-! Finite Euler–Poincare identities over fields, including the degree-zero formula when positive cohomology vanishes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

theorem cochain_euler_sum_with_boundary {K : Type u} [Field K]
    (D : CochainComplex (ModuleCat.{u} K) ℕ)
    (hfinite : ∀ q, Module.Finite K (D.X q)) (N : ℕ) :
    (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.X q) : ℤ)) =
      (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.homology q) : ℤ)) +
        (-1 : ℤ) ^ N * (Module.finrank K (LinearMap.range (D.d N (N + 1)).hom) : ℤ) := by
  apply AlternatingConeSums.alternating_dimension_telescope
  · have := hfinite 0
    exact_mod_cast Cochain.DimensionBalance.cochain_dimension_balance_zero D
  · intro q
    have := hfinite q
    have := hfinite (q + 1)
    exact_mod_cast Cochain.DimensionBalance.cochain_dimension_balance_succ D q

theorem cochain_euler_sum_of_final_zero {K : Type u} [Field K]
    (D : CochainComplex (ModuleCat.{u} K) ℕ)
    (hfinite : ∀ q, Module.Finite K (D.X q)) (N : ℕ) (hfinal : IsZero (D.X (N + 1))) :
    (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.X q) : ℤ)) =
      (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.homology q) : ℤ)) := by
  have : Subsingleton (D.X (N + 1)) := ModuleCat.isZero_iff_subsingleton.mp hfinal
  have hb : Module.finrank K (LinearMap.range (D.d N (N + 1)).hom) = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hb, Nat.cast_zero, mul_zero, add_zero] using cochain_euler_sum_with_boundary D hfinite N

theorem cochain_euler_sum_of_positive_exact {K : Type u} [Field K]
    (D : CochainComplex (ModuleCat.{u} K) ℕ)
    (hfinite : ∀ q, Module.Finite K (D.X q)) (N : ℕ) (hfinal : IsZero (D.X (N + 1)))
    (hexact : ∀ q, D.ExactAt (q + 1)) :
    (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.X q) : ℤ)) =
      (Module.finrank K (D.homology 0) : ℤ) := by
  rw [cochain_euler_sum_of_final_zero D hfinite N hfinal]
  have hh (q : ℕ) : Module.finrank K (D.homology (q + 1)) = 0 := by
    have : Subsingleton (D.homology (q + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mp (hexact q).isZero_homology
    exact Module.finrank_zero_of_subsingleton
  rw [Finset.sum_eq_single 0]
  · simp
  · intro q _ hq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    rw [hh j]
    simp
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ComplexEulerFormula
