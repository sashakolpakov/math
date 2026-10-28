import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Polynomial
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Poincare Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PoincareExact.Poincare

noncomputable section

/-!
# Cohomology: exactness of the completed divided-polynomial de Rham sequence

The explicit integral primitive gives exactness, including after adic
completion. This packages the local Poincaré calculation in the homological
language used by the global comparison constructions.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Polynomial.DividedPolynomial

universe u

variable (R : Type u) [CommRing R]

theorem differential_constant : (Divided.Polynomial.DividedPolynomial.differential R).comp (Divided.Polynomial.DividedPolynomial.constant R) = 0 := by
  apply LinearMap.ext
  intro a
  apply Finsupp.ext
  intro n
  simp [Divided.Polynomial.DividedPolynomial.constant, Divided.Polynomial.DividedPolynomial.differential]

theorem evaluation_constant : (Divided.Polynomial.DividedPolynomial.evaluation R).comp (Divided.Polynomial.DividedPolynomial.constant R) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  simp [Divided.Polynomial.DividedPolynomial.evaluation, Divided.Polynomial.DividedPolynomial.constant]

/-- The augmented integral one-variable divided-polynomial de Rham sequence. -/
def sequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (Divided.Polynomial.DividedPolynomial.constant R) (Divided.Polynomial.DividedPolynomial.differential R) (differential_constant R)

theorem sequence_shortExact : (sequence R).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro f
    change Divided.Polynomial.DividedPolynomial.Coefficients R at f
    change Divided.Polynomial.DividedPolynomial.differential R f = 0 ↔ ∃ a, Divided.Polynomial.DividedPolynomial.constant R a = f
    constructor
    · intro hf
      exact ⟨f 0, (Divided.Polynomial.DividedPolynomial.differential_eq_zero_iff R f).mp hf |>.symm⟩
    · rintro ⟨a, rfl⟩
      exact LinearMap.congr_fun (differential_constant R) a
  · change Function.Injective (Divided.Polynomial.DividedPolynomial.constant R)
    exact Function.LeftInverse.injective
      (g := Divided.Polynomial.DividedPolynomial.evaluation R)
      (fun a => LinearMap.congr_fun (evaluation_constant R) a)
  · exact Divided.Polynomial.DividedPolynomial.differential_surjective R

variable (I : Ideal R)

/-- The augmented sequence after adic completion. -/
def completedSequence : ShortComplex (ModuleCat.{u} (AdicCompletion I R)) :=
  ShortComplex.moduleCatMk (AdicCompletion.map I (Divided.Polynomial.DividedPolynomial.constant R))
    (AdicCompletion.map I (Divided.Polynomial.DividedPolynomial.differential R)) (by
      apply LinearMap.ext
      intro a
      rw [LinearMap.comp_apply, AdicCompletion.map_comp_apply, differential_constant,
        AdicCompletion.map_zero, LinearMap.zero_apply])

/-- The completed Poincaré sequence remains short exact. -/
theorem completedSequence_shortExact : (completedSequence R I).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact Divided.Polynomial.DividedPolynomial.completed_differential_eq_zero_iff R I
  · change Function.Injective (AdicCompletion.map I (Divided.Polynomial.DividedPolynomial.constant R))
    apply Function.LeftInverse.injective (g := AdicCompletion.map I (Divided.Polynomial.DividedPolynomial.evaluation R))
    intro a
    rw [AdicCompletion.map_comp_apply, evaluation_constant, AdicCompletion.map_id,
      LinearMap.id_apply]
  · exact Divided.Polynomial.DividedPolynomial.completed_differential_surjective R I

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PoincareExact.Poincare
