import OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductScalar

/-! # Positive Product Uniform Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductUniformDetection

noncomputable section

/-! Uniform lifting of degree-one classes and a uniform annihilator of
integral products force the corresponding source product to be torsion,
when a family of genuine finite comparison maps detects source classes. -/

universe u v w z
variable {H : ℕ → Type u} {K : ℕ → Type v} {L : ℕ → ℕ → Type w}
  [∀ i, AddCommGroup (H i)] [∀ i, AddCommGroup (K i)]
  [∀ n i, AddCommGroup (L n i)]
  {R : Type z} [CommRing R] [∀ n i, Module R (L n i)]
  (μ : ∀ i j, H i → H j → H (i+j))
  (ν : ∀ i j, K i → K j → K (i+j))
  (σ : ∀ n i j, L n i →ₗ[R] L n j →ₗ[R] L n (i+j))
  (f : ∀ n i, H i →+ L n i) (r : ∀ n i, K i →+ L n i)
  (hf : ∀ n i j x y, f n (i+j) (μ i j x y) = σ n i j (f n i x) (f n j y))
  (hr : ∀ n i j x y, r n (i+j) (ν i j x y) = σ n i j (r n i x) (r n j y))
  (hdetect : ∀ i (x : H i), (∀ n, f n i x = 0) → x = 0)

include hf hr hdetect in
theorem annihilation (d b c : ℕ)
    (hlift : ∀ n (x : L n 1), ∃ y : K 1, r n 1 y = c • x)
    (hkill : ∀ y : Fin (d+1) → K 1, b • GradedPositiveProduct.product ν d y = 0)
    (v : Fin (d+1) → H 1) :
    (b*c^(d+1)) • GradedPositiveProduct.product μ d v = 0 := by
  classical
  apply hdetect (d+1)
  intro n
  choose y hy using fun i : Fin (d+1) => hlift n (f n 1 (v i))
  have hprod : r n (d+1) (GradedPositiveProduct.product ν d y) =
      c^(d+1) • f n (d+1) (GradedPositiveProduct.product μ d v) := by
    calc
      _ = GradedPositiveProduct.product (fun i j a b => σ n i j a b) d
          (fun i => r n 1 (y i)) := GradedPositiveProduct.natural ν (fun i j a b => σ n i j a b)
            (fun i => r n i) (fun i j x y => hr n i j x y) d y
      _ = GradedPositiveProduct.product (fun i j a b => σ n i j a b) d
          (fun i => c • f n 1 (v i)) :=
        congrArg (GradedPositiveProduct.product (fun i j a b => σ n i j a b) d) (funext hy)
      _ = c^(d+1) • GradedPositiveProduct.product (fun i j a b => σ n i j a b) d
          (fun i => f n 1 (v i)) := PositiveProductScalar.nsmul (σ n) c d _
      _ = _ := congrArg (c^(d+1) • ·) (GradedPositiveProduct.natural μ (fun i j a b => σ n i j a b)
            (fun i => f n i) (fun i j x y => hf n i j x y) d v).symm
  have hz : b • r n (d+1) (GradedPositiveProduct.product ν d y) = 0 := by
    simpa only [map_nsmul, map_zero] using congrArg (r n (d+1)) (hkill y)
  rw [hprod, smul_smul] at hz
  simpa only [map_nsmul] using hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductUniformDetection
