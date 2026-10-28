import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedExteriorCup

/-! # Graded Positive Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct

/-! Products of a nonempty list of degree-one classes use only positive
degrees. Their naturality needs no normalization of a degree-zero unit. -/

universe u v

variable {H : ℕ → Type u} (μ : ∀ i j, H i → H j → H (i+j))

def product : (n : ℕ) → (Fin (n+1) → H 1) → H (n+1)
  | 0, x => x 0
  | n+1, x => μ (n+1) 1 (product n (Fin.init x)) (x (Fin.last (n+1)))

variable {K : ℕ → Type v} (ν : ∀ i j, K i → K j → K (i+j))
  (f : ∀ i, H i → K i)
  (hf : ∀ i j x y, f (i+j) (μ i j x y) = ν i j (f i x) (f j y))

include hf in
theorem natural (n : ℕ) (x : Fin (n+1) → H 1) :
    f (n+1) (GradedPositiveProduct.product μ n x) = GradedPositiveProduct.product ν n (fun i => f 1 (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GradedPositiveProduct.product, hf, ih, GradedPositiveProduct.product]
      rfl

variable {R : Type*} [CommRing R] (D : GradedCupAlgebra.Data R)

theorem iterated_eq (n : ℕ) (x : Fin (n+1) → D.H 1) :
    GradedExteriorCup.iterated D (n+1) x =
      GradedPositiveProduct.product (fun i j a b => D.cup i j a b) n x := by
  induction n with
  | zero =>
      change D.cup 0 1 D.one (x 0) = x 0
      exact D.one_cup 1 (x 0)
  | succ n ih =>
      rw [GradedExteriorCup.iterated, GradedPositiveProduct.product, ih]

theorem exteriorPowerCup_ne_zero (n : ℕ) (x : Fin (n+1) → D.H 1)
    (hx : GradedPositiveProduct.product (fun i j a b => D.cup i j a b) n x ≠ 0) :
    GradedExteriorCup.exteriorPowerCup D (n+1) ≠ 0 :=
  GradedExteriorCup.exteriorPowerCup_ne_zero D (n+1) x
    ((iterated_eq D n x).symm ▸ hx)

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct
