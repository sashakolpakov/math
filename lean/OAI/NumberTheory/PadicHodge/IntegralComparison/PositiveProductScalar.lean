import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveMultilinear

/-! # Positive Product Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductScalar

noncomputable section

/-! Simultaneously scaling the degree-one inputs of the genuine
positive product scales it by the corresponding power. -/

universe u v
variable {R : Type u} [CommRing R] {H : ℕ → Type v}
  [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
  (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i+j))

theorem smul (a : R) (d : ℕ) (x : Fin (d+1) → H 1) :
    GradedPositiveProduct.product (fun i j x y => μ i j x y) d (fun i => a • x i) =
      a^(d+1) • GradedPositiveProduct.product (fun i j x y => μ i j x y) d x := by
  simpa only [GradedPositiveMultilinear.map_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using
      (GradedPositiveMultilinear.map μ d).map_smul_univ (fun _ => a) x

theorem nsmul (a d : ℕ) (x : Fin (d+1) → H 1) :
    GradedPositiveProduct.product (fun i j x y => μ i j x y) d (fun i => a • x i) =
      a^(d+1) • GradedPositiveProduct.product (fun i j x y => μ i j x y) d x := by
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using smul μ (a : R) d x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductScalar
