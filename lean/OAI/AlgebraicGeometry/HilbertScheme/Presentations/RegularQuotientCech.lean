import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ShiftedCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing

/-! # Regular Quotient Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularQuotientCech.ProjectiveCech

noncomputable section

/-!
Eventual Čech vanishing descends to the bound of a regular degree-one
quotient. This is the exact-sequence step in a uniform regularity argument.
-/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ShiftedCech.GradedModules

universe u v w

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [Module.Finite (MvPolynomial σ R) M]
variable {P : Type w} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℙ : ℤ → Submodule R P) [Decomposition ℙ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℙ]

theorem moduleCech_exact_of_regular_quotient
    (i : M →ₗ[MvPolynomial σ R] M) (p : M →ₗ[MvPolynomial σ R] P)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ ℳ (d + 1))
    (hp : ∀ d m, m ∈ ℳ d → p m ∈ ℙ d)
    (hinj : Function.Injective i) (hsurj : Function.Surjective p) (hex : Function.Exact i p)
    (D : ℤ) (hP : ∀ d : ℤ, D ≤ d → ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R P ℙ d q) :
    ∀ d : ℤ, D ≤ d → ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  have hshift : ∀ d m, m ∈ ReindexedGrading.GradedModules.shiftedGrading ℳ (-1) d → i m ∈ ℳ d := by
    intro d m hm
    have h := hi (d + -1) m hm
    simpa only [neg_add_cancel_right] using h
  obtain ⟨B, hB⟩ := Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness (σ := σ) R M ℳ
  have H : ∀ k : ℕ, ∀ d : ℤ, D ≤ d → (B : ℤ) ≤ d + (k : ℤ) →
      ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
    intro k
    induction k with
    | zero =>
      intro d _ hd q
      exact hB d (by simpa only [Nat.cast_zero, add_zero] using hd) q
    | succ k ih =>
      intro d hd hBd q
      have hnext := ih (d + 1) (by omega) (by push_cast at hBd ⊢; omega)
      have hs : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M (ReindexedGrading.GradedModules.shiftedGrading ℳ (-1)) (d + 1) q := by
        cases q with
        | zero =>
          exact Cech.ExactLeft.ProjectiveCech.moduleCechExactAt_zero_of_injective (σ := σ) R M (ReindexedGrading.GradedModules.shiftedGrading ℳ (-1)) ℳ
            i hshift hinj (d + 1) (hnext 0)
        | succ q =>
          exact Cech.ExactLeft.ProjectiveCech.moduleCech_exact_left (σ := σ) R M (ReindexedGrading.GradedModules.shiftedGrading ℳ (-1)) ℳ ℙ
            i p hshift hp hinj hsurj hex (d + 1) q (hnext (q + 1)) (hP (d + 1) (by omega) q)
      have ht := (ShiftedCech.ProjectiveCech.moduleCechExactAt_shifted (σ := σ) R M ℳ (-1) (d + 1) q).mp hs
      simpa only [add_neg_cancel_right] using ht
  intro d hd q
  exact H ((B : ℤ) - d).toNat d hd (by omega) q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularQuotientCech.ProjectiveCech
