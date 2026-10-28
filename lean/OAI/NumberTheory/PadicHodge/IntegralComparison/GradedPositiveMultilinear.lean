import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultilinearSpanningNonzero

/-! # Graded Positive Multilinear -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveMultilinear

noncomputable section

/-! Nonempty iterated cup products are genuine multilinear maps, so a
nonzero product is detected on any scalar-extension spanning family. -/

open scoped TensorProduct

universe u v
variable {S : Type u} [CommRing S] {H : ℕ → Type v}
  [∀ n, AddCommGroup (H n)] [∀ n, Module S (H n)]
  (μ : ∀ i j, H i →ₗ[S] H j →ₗ[S] H (i+j))

def map : (n : ℕ) → MultilinearMap S (fun _ : Fin (n+1) => H 1) (H (n+1))
  | 0 => MultilinearMap.ofSubsingleton S (H 1) (H 1) (0 : Fin 1) LinearMap.id
  | n+1 => ((μ (n+1) 1).compMultilinearMap (map n)).uncurryRight

theorem map_apply (n : ℕ) (v : Fin (n+1) → H 1) :
    GradedPositiveMultilinear.map μ n v = GradedPositiveProduct.product (fun i j x y => μ i j x y) n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change μ (n+1) 1 (GradedPositiveMultilinear.map μ n (Fin.init v)) (v (Fin.last (n+1))) = _
      rw [ih]
      rfl

variable {R : Type*} [CommRing R] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M]
  (e : S ⊗[R] M →ₗ[S] H 1) (he : Function.Surjective e)

include he in
theorem scalar_exists_nonzero (n : ℕ)
    (h : ∃ v : Fin (n+1) → H 1,
      GradedPositiveProduct.product (fun i j x y => μ i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → M,
      GradedPositiveProduct.product (fun i j x y => μ i j x y) n
        (fun i => e ((1 : S) ⊗ₜ[R] v i)) ≠ 0 := by
  simpa only [map_apply] using MultilinearSpanningNonzero.scalar_exists_nonzero e he
    (n+1) (GradedPositiveMultilinear.map μ n) (by simpa only [map_apply] using h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveMultilinear
