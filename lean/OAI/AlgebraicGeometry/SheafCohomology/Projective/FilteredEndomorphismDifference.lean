import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Tactic.Abel

/-! # Filtered Endomorphism Difference -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference

/-! Removing an invertible filtration-preserving factor from a difference that lowers a filtration. -/

theorem endomorphism_difference_mem_of_product {G : Type*} [AddCommGroup G]
    (F H : AddSubgroup G) (T U V : AddMonoid.End G) (hUV : U * V = 1)
    (hV : ∀ x ∈ F, V x ∈ F)
    (hTU : ∀ x ∈ F, (T * U - 1) x ∈ H) (hU : ∀ x ∈ F, (U - 1) x ∈ H)
    (x : G) (hx : x ∈ F) : (T - 1) x ∈ H := by
  have hvx := hV x hx
  have he : U (V x) = x := by
    change (U * V) x = x
    rw [hUV]
    rfl
  have h := H.sub_mem (hTU (V x) hvx) (hU (V x) hvx)
  change (T (U (V x)) - V x) - (U (V x) - V x) ∈ H at h
  rw [he] at h
  change T x - x ∈ H
  convert h using 1
  abel

theorem endomorphism_pow_mem_filtration {G : Type*} [AddCommGroup G]
    (F : ℕ → AddSubgroup G) (T : AddMonoid.End G)
    (hT : ∀ d x, x ∈ F (d + 1) → T x ∈ F d) (r d : ℕ)
    (x : G) (hx : x ∈ F (d + r)) : (T ^ r) x ∈ F d := by
  induction r generalizing x with
  | zero => simpa only [Nat.add_zero, pow_zero, AddMonoid.End.one_apply] using hx
  | succ r ih =>
      rw [pow_succ]
      change (T ^ r) (T x) ∈ F d
      apply ih
      apply hT (d + r) x
      simpa only [Nat.add_assoc] using hx

theorem endomorphism_pow_eq_zero_of_filtration {G : Type*} [AddCommGroup G]
    (F : ℕ → AddSubgroup G) (hF : F 0 = ⊥) (T : AddMonoid.End G)
    (hT : ∀ d x, x ∈ F (d + 1) → T x ∈ F d) (r : ℕ)
    (x : G) (hx : x ∈ F r) : (T ^ r) x = 0 := by
  have h := endomorphism_pow_mem_filtration F T hT r 0 x (by simpa only [Nat.zero_add] using hx)
  simpa only [hF, AddSubgroup.mem_bot] using h

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference
