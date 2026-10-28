import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler

/-! # Complex Euler Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexEulerLength

noncomputable section

/-! The Euler characteristic of a bounded complex of finite-length modules
agrees with that of its actual homology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

def boundaryLength (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) : ℚ :=
  ExactLength.rationalLength R (.of R (LinearMap.range (K.d (n + 1) n).hom))

theorem degree_zero (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (h : Module.length R (K.X 0) ≠ ⊤) :
    ExactLength.rationalLength R (K.X 0) = ExactLength.rationalLength R (K.homology 0) + boundaryLength R K 0 := by
  have h₀ := HomologyLength.middle_length R (K.sc' 1 0 0) h
  have he := congrArg (fun a : ℕ∞ => (a.toNat : ℚ))
    (K.homologyIsoSc' 1 0 0 (by simp) (by simp)).toLinearEquiv.length_eq
  have hz := ExactLength.rationalLength_range_of_zero R (K.d 0 0) (K.shape _ _ (by simp))
  change ExactLength.rationalLength R (K.X 0) = ExactLength.rationalLength R (K.sc' 1 0 0).homology +
    boundaryLength R K 0 + ExactLength.rationalLength R (.of R (LinearMap.range (K.d 0 0).hom)) at h₀
  change ExactLength.rationalLength R (K.homology 0) = ExactLength.rationalLength R (K.sc' 1 0 0).homology at he
  rw [← he, hz, add_zero] at h₀
  exact h₀

theorem degree_succ (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (h : Module.length R (K.X (n + 1)) ≠ ⊤) :
    ExactLength.rationalLength R (K.X (n + 1)) = ExactLength.rationalLength R (K.homology (n + 1)) +
      boundaryLength R K (n + 1) + boundaryLength R K n := by
  have h₀ := HomologyLength.middle_length R (K.sc' (n + 2) (n + 1) n) h
  have he := congrArg (fun a : ℕ∞ => (a.toNat : ℚ))
    (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).toLinearEquiv.length_eq
  change ExactLength.rationalLength R (K.X (n + 1)) = ExactLength.rationalLength R (K.sc' (n + 2) (n + 1) n).homology +
    boundaryLength R K (n + 1) + boundaryLength R K n at h₀
  change ExactLength.rationalLength R (K.homology (n + 1)) =
    ExactLength.rationalLength R (K.sc' (n + 2) (n + 1) n).homology at he
  rw [← he] at h₀
  exact h₀

theorem homology_euler_eq (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (h : ∀ n, Module.length R (K.X n) ≠ ⊤) (d : ℕ) (hd : IsZero (K.X (d + 1))) :
    (∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * ExactLength.rationalLength R (K.homology n)) =
      ∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * ExactLength.rationalLength R (K.X n) := by
  have hs := Tor.Euler.alternating_identity
    (fun n => ExactLength.rationalLength R (K.X n))
    (fun n => ExactLength.rationalLength R (K.homology n)) (fun _ => 0) (boundaryLength R K)
    (by simpa only [add_zero] using degree_zero R K (h 0))
    (fun n => by simpa only [add_zero] using degree_succ R K n (h (n + 1))) d
  have hz : boundaryLength R K d = 0 :=
    ExactLength.rationalLength_range_of_zero R _ (hd.eq_of_src _ _)
  simpa only [mul_zero, Finset.sum_const_zero, add_zero, hz, sub_zero] using hs

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexEulerLength
