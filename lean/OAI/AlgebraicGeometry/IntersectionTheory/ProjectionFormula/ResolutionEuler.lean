import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexEulerLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FreeTensorLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution
import Mathlib.Algebra.Homology.SingleHomology

/-! # Resolution Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionEuler

noncomputable section

/-! Finite free resolutions compute local Tor Euler characteristics by
the alternating ranks of their terms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

theorem resolution_length (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (h : ∀ n, Module.length R (P.complex.X n) ≠ ⊤)
    (d : ℕ) (hd : IsZero (P.complex.X (d + 1))) :
    ExactLength.rationalLength R M =
      ∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * ExactLength.rationalLength R (P.complex.X n) := by
  have hz (n : ℕ) : ExactLength.rationalLength R (P.complex.homology (n + 1)) = 0 := by
    let := ModuleCat.subsingleton_of_isZero
      (IsZero.of_iso
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 M (n + 1) (by omega))
        (isoOfQuasiIsoAt P.π (n + 1)))
    simp [ExactLength.rationalLength, Module.length_eq_zero]
  have h₀ : ExactLength.rationalLength R (P.complex.homology 0) = ExactLength.rationalLength R M := by
    exact congrArg (fun a : ℕ∞ => (a.toNat : ℚ))
      ((isoOfQuasiIsoAt P.π 0) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).toLinearEquiv.length_eq
  have he := ComplexEulerLength.homology_euler_eq R P.complex h d hd
  rw [Finset.sum_range_succ'] at he
  simpa only [hz, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mul, h₀] using he

theorem tor_euler_rank_sum [Nontrivial R] (M N : ModuleCat.{u} R)
    (hM : Module.length R M ≠ ⊤) (P : ProjectiveResolution N)
    (hP : ∀ n, Module.Finite R (P.complex.X n) ∧ Module.Free R (P.complex.X n))
    (d : ℕ) (hd : IsZero (P.complex.X (d + 1))) :
    Tor.Euler.euler R M N d = ExactLength.rationalLength R M *
      ∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * (Module.finrank R (P.complex.X n) : ℚ) := by
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hK (n : ℕ) : Module.length R (K.X n) ≠ ⊤ := by
    let := (hP n).1
    let := (hP n).2
    exact FreeTensorLength.tensor_length_ne_top R M (P.complex.X n) hM
  have hdK : IsZero (K.X (d + 1)) := (tensorLeft M).map_isZero hd
  calc
    Tor.Euler.euler R M N d =
        ∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * ExactLength.rationalLength R (K.homology n) := by
      apply Finset.sum_congr rfl
      intro n _
      exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ n * (a.toNat : ℚ))
        (P.isoLeftDerivedObj (tensorLeft M) n).toLinearEquiv.length_eq
    _ = ∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * ExactLength.rationalLength R (K.X n) :=
      ComplexEulerLength.homology_euler_eq R K hK d hdK
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      let := (hP n).1
      let := (hP n).2
      change (-1 : ℚ) ^ n * ExactLength.rationalLength R (.of R (M ⊗[R] P.complex.X n)) = _
      rw [FreeTensorLength.tensor_rationalLength]
      ring

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionEuler
