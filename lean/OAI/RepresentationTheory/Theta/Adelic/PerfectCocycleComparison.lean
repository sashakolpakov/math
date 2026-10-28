import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot
import Mathlib.GroupTheory.Abelianization.Defs

/-! # Perfect Cocycle Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.PerfectCocycleComparison

noncomputable section

/-! Two continuous square-root cocycles on a connected base agree
when the acting group is perfect. Only continuity in the base is
needed; no Lie-group infrastructure or parameter-continuity assumption
is introduced. -/

open OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

variable {G X : Type*} [Group G] [TopologicalSpace X] [PreconnectedSpace X] [MulAction G X]

theorem perfect_square_cocycles_eq (hG : commutator G = ⊤) (x₀ : X)
    (f j : G → X → ℂ) (hf : ∀ g, Continuous (f g)) (hj : ∀ g, Continuous (j g))
    (hfn : ∀ g x, f g x ≠ 0) (hjn : ∀ g x, j g x ≠ 0)
    (hs : ∀ g x, f g x ^ 2 = j g x ^ 2)
    (hfm : ∀ g h x, f (g * h) x = f g (h • x) * f h x)
    (hjm : ∀ g h x, j (g * h) x = j g (h • x) * j h x)
    (hf1 : ∀ x, f 1 x = 1) (hj1 : ∀ x, j 1 x = 1) : f = j := by
  let q := fun g => f g x₀ / j g x₀
  have hq (g : G) : q g ^ 2 = 1 := by
    dsimp only [q]
    rw [div_pow, hs]
    exact div_self (pow_ne_zero 2 (hjn g x₀))
  have he (g : G) (x : X) : f g x = q g * j g x := by
    have h := ContinuousSquareRoot.continuous_square_roots_eq (f g) (fun x => q g * j g x)
      (hf g) (continuous_const.mul (hj g)) (hfn g)
      (fun x => by rw [mul_pow, hq, one_mul, hs]) x₀ (by
        dsimp only [q]
        rw [div_mul_cancel₀ _ (hjn g x₀)])
    exact congrFun h x
  have hqm (g h : G) : q (g * h) = q g * q h := by
    apply mul_right_cancel₀ (hjn (g * h) x₀)
    rw [← he, hfm, he g, he h, hjm]
    ring
  let χ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 (q g) (div_ne_zero (hfn g x₀) (hjn g x₀))
      map_one' := by
        apply Units.ext
        change q 1 = 1
        dsimp only [q]
        rw [hf1, hj1, div_one]
      map_mul' := fun g h => Units.ext (hqm g h) }
  have hχ (g : G) : χ g = 1 := by
    apply Abelianization.commutator_subset_ker χ
    rw [hG]
    trivial
  funext g x
  have hq1 : q g = 1 := congrArg Units.val (hχ g)
  rw [he, hq1, one_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.PerfectCocycleComparison
