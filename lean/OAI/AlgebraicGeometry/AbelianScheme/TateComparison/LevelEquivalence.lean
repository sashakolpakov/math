import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Level Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelEquivalence.Tate

noncomputable section

/-! A point map bijective on every finite torsion group is bijective on
the actual Tate inverse limits. No surjectivity on the full point groups
is required. -/

universe u
variable (q : ℕ) [Fact q.Prime] {H H' : Type u} [AddCommGroup H] [AddCommGroup H']
  (f : H →+ H') (hf : ∀ n, Function.Bijective (Add.Tate.mapLevel q f n))

include hf in
theorem map_bijective_of_levels : Function.Bijective (Add.Tate.map q f) := by
  let e (n : ℕ) := LinearEquiv.ofBijective (Add.Tate.mapLevel q f n) (hf n)
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    exact (hf n).1 (congrArg (fun z : Add.Tate.Module (H := H') q => z.val n) h)
  · intro y
    let x : Add.Tate.Module (H := H) q := ⟨fun n => (e n).symm (y.val n), by
      intro n
      apply (hf n).1
      rw [Add.Tate.mapLevel_transition]
      change Add.Tate.transition q n (e (n + 1) ((e (n + 1)).symm (y.val (n + 1)))) =
        e n ((e n).symm (y.val n))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact y.property n⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply (y.val n)

def equivalenceOfLevels : Add.Tate.Module (H := H) q ≃ₗ[ℤ_[q]] Add.Tate.Module (H := H') q :=
  LinearEquiv.ofBijective (Add.Tate.map q f) (map_bijective_of_levels q f hf)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelEquivalence.Tate
