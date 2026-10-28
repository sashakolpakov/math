import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.SectionMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion

/-! # Tensor Irrelevant Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion.ProjectiveCech

noncomputable section

/-! High homogeneous degrees remain free of irrelevant torsion after arbitrary tensor base change. -/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion.GradedModules

universe u v w

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [Module.Finite (MvPolynomial σ R) M]

theorem eventual_tensor_no_irrelevant_torsion
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0)) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      ∀ (S : Type w) [AddCommGroup S] [Module R S], ∀ x : TensorProduct R S (ℳ d),
        (∀ i : σ, ∃ k : ℕ, ((TensorFractionTorsion.GradedModules.moduleScalarEnd (R := R) M (X (R := R) i ^ k)).lTensor S)
          (((ℳ d).subtype.lTensor S) x) = 0) → x = 0 := by
  obtain ⟨B, hB⟩ := Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_eventual_lTensor_injective (σ := σ) R M ℳ hflat
  refine ⟨B, fun d hd S _ _ x hx => ?_⟩
  apply hB d hd S
  rw [map_zero]
  apply (TensorProduct.piRight R R S (fun s : Finset σ => Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s)).injective
  rw [map_zero]
  funext s
  rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_tensor_coordinate, Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_proj]
  by_cases hs : s.card = 1
  · rw [ite_eq_left hs, LinearMap.lTensor_comp_apply]
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    obtain ⟨k, hk⟩ := hx i
    exact TensorFractionTorsion.GradedModules.tensorFraction_zero_of_power_torsion M (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (X i) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi)
      S _ k hk
  · rw [ite_eq_right hs, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion.ProjectiveCech
