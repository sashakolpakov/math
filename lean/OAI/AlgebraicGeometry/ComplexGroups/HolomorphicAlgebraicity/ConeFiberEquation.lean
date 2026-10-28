import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoefficientScaling
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HomogeneousExtension

/-! # Cone Fiber Equation -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeFiberEquation.Constructions.Cone

noncomputable section

section

/-!
# Polynomial coefficients of the cone-fiber equation

The scaling law makes each lower coefficient positively homogeneous. The
punctured homogeneous extension theorem makes it an actual homogeneous
polynomial, while the leading coefficient is the constant one.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem exists_polynomial_coefficients_of_scaling {n d : ℕ}
    {P : (Fin n → ℂ) → ℂ[X]}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {0}ᶜ)
    (hP : ∀ y, y ≠ 0 → (P y).Monic ∧ (P y).natDegree = d)
    (hscale : ∀ t : ℂ, t ≠ 0 → ∀ x, x ≠ 0 → P (t • x) = (P x).scaleRoots t) :
    ∃ a : Fin (d + 1) → MvPolynomial (Fin n) ℂ,
      (∀ j, (a j).IsHomogeneous (d - j.val)) ∧
      ∀ j x, x ≠ 0 → MvPolynomial.eval x (a j) = (P x).coeff j.val := by
  have hex (j : Fin (d + 1)) : ∃ a : MvPolynomial (Fin n) ℂ,
      a.IsHomogeneous (d - j.val) ∧ ∀ x, x ≠ 0 → MvPolynomial.eval x a = (P x).coeff j.val := by
    by_cases hj : j.val = d
    · refine ⟨1, ?_, ?_⟩
      · simpa only [hj, Nat.sub_self] using MvPolynomial.isHomogeneous_one (Fin n) ℂ
      · intro x hx
        rw [map_one, hj, ← (hP x hx).2]
        exact (hP x hx).1.coeff_natDegree.symm
    · have hpos : 0 < d - j.val := by have := j.isLt; omega
      apply HomogeneousExtension.Constructions.Growth.extend_punctured_homogeneous hpos (hcoeff j.val)
      intro t ht x hx
      rw [hscale t ht x hx, coeff_scaleRoots, (hP x hx).2, mul_comm]
  choose a ha heq using hex
  exact ⟨a, ha, heq⟩

def fiberCoordinates {n : ℕ} (y : Fin n → ℂ) (z : ℂ) : Option (Fin n) → ℂ :=
  fun i => i.elim z y

theorem exists_homogeneous_fiber_equation_of_scaling {n d : ℕ}
    {P : (Fin n → ℂ) → ℂ[X]}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {0}ᶜ)
    (hP : ∀ y, y ≠ 0 → (P y).Monic ∧ (P y).natDegree = d)
    (hscale : ∀ t : ℂ, t ≠ 0 → ∀ x, x ≠ 0 → P (t • x) = (P x).scaleRoots t) :
    ∃ F : MvPolynomial (Option (Fin n)) ℂ,
      F.IsHomogeneous d ∧
      ∀ y, y ≠ 0 → ∀ z : ℂ, MvPolynomial.eval (fiberCoordinates y z) F = (P y).eval z := by
  classical
  obtain ⟨a, ha, heq⟩ := exists_polynomial_coefficients_of_scaling hcoeff hP hscale
  let F : MvPolynomial (Option (Fin n)) ℂ :=
    ∑ j : Fin (d + 1), MvPolynomial.rename some (a j) * MvPolynomial.X none ^ j.val
  refine ⟨F, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum Finset.univ _ d
    intro j _
    have hmul := ((ha j).rename_isHomogeneous (f := some)).mul ((MvPolynomial.isHomogeneous_X ℂ
      (none : Option (Fin n))).pow j.val)
    convert hmul using 1
    have := j.isLt
    omega
  · intro y hy z
    simp only [F, map_sum, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_X]
    change (∑ j : Fin (d + 1), MvPolynomial.eval y (a j) * z ^ j.val) = (P y).eval z
    simp_rw [heq _ y hy]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (P y).coeff j * z ^ j)]
    exact (eval_eq_sum_range' (show (P y).natDegree < d + 1 from by rw [(hP y hy).2]; omega) z).symm

theorem exists_generic_homogeneous_fiber_equation {n : ℕ} (hn : 0 < n)
    {S : Set ((Fin n → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ p ∈ S, p ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S p)
    (hcone : ∀ t : ℂ, ∀ p ∈ S, t • p ∈ S) :
    ∃ (d : ℕ) (F : MvPolynomial (Option (Fin n)) ℂ),
      F.IsHomogeneous d ∧ F ≠ 0 ∧
      ∀ x, x ≠ 0 → ∃ (V : Set (Fin n → ℂ)) (c : (Fin n → ℂ) → ℂ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ {0}ᶜ ∧ DifferentiableOn ℂ c V ∧
        (¬∀ᶠ y in 𝓝 x, c y = 0) ∧ V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
        ∀ y ∈ V, c y ≠ 0 → ∀ z : ℂ,
          (y, z) ∈ S ↔ MvPolynomial.eval (fiberCoordinates y z) F = 0 := by
  obtain ⟨d, P, hcoeff, hP, hnear⟩ := PuncturedFiberPolynomial.Constructions.Cone.exists_punctured_fiber_polynomial hn hproper hfinite hlocal
  have hnear' (x : Fin n → ℂ) (hx : x ≠ 0) := hnear x hx
  have hscale (t : ℂ) (ht : t ≠ 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
      P (t • x) = (P x).scaleRoots t := by
    apply ConeCoefficientScaling.Constructions.Cone.fiber_polynomial_scaleRoots hcone hcoeff hP _ ht hx
    intro y hy
    obtain ⟨V, c, hV, hyV, hV0, hc, hcn, _, hroot⟩ := hnear' y hy
    exact ⟨V, c, hV, hyV, hV0, hc, hcn, hroot⟩
  obtain ⟨F, hF, hFeq⟩ := exists_homogeneous_fiber_equation_of_scaling hcoeff hP hscale
  have hFne : F ≠ 0 := by
    intro hzero
    let y : Fin n → ℂ := fun _ => 1
    have hy : y ≠ 0 := by
      intro hy
      have h := congrFun hy ⟨0, hn⟩
      exact one_ne_zero h
    apply (hP y hy).1.ne_zero
    apply Polynomial.zero_of_eval_zero
    intro z
    rw [← hFeq y hy z, hzero, map_zero]
  refine ⟨d, F, hF, hFne, ?_⟩
  intro x hx
  obtain ⟨V, c, hV, hxV, hV0, hc, hcn, hdense, hroot⟩ := hnear x hx
  refine ⟨V, c, hV, hxV, hV0, hc, hcn, hdense, ?_⟩
  intro y hy hcy z
  rw [hFeq y (hV0 hy) z]
  exact (hroot y hy hcy).2 z

end

/-!
# The monic term of a homogeneous cone-fiber equation

The homogeneous equation can be chosen to restrict to exactly `z ^ d` on
the vertical axis. This also controls the fiber over the cone vertex.
-/

open Set _root_.Polynomial

theorem exists_monic_homogeneous_fiber_equation_of_scaling {n d : ℕ}
    {P : (Fin n → ℂ) → ℂ[X]}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {0}ᶜ)
    (hP : ∀ y, y ≠ 0 → (P y).Monic ∧ (P y).natDegree = d)
    (hscale : ∀ t : ℂ, t ≠ 0 → ∀ x, x ≠ 0 → P (t • x) = (P x).scaleRoots t) :
    ∃ F : MvPolynomial (Option (Fin n)) ℂ,
      F.IsHomogeneous d ∧
      (∀ y, y ≠ 0 → ∀ z : ℂ, MvPolynomial.eval (fiberCoordinates y z) F = (P y).eval z) ∧
      ∀ z : ℂ, MvPolynomial.eval (fiberCoordinates 0 z) F = z ^ d := by
  classical
  obtain ⟨a, ha, heq⟩ := exists_polynomial_coefficients_of_scaling hcoeff hP hscale
  let b : Fin (d + 1) → MvPolynomial (Fin n) ℂ := fun j => if j.val = d then 1 else a j
  have hb (j : Fin (d + 1)) : (b j).IsHomogeneous (d - j.val) := by
    by_cases hj : j.val = d
    · simpa only [b, ite_eq_left hj, hj, Nat.sub_self] using MvPolynomial.isHomogeneous_one (Fin n) ℂ
    · simpa only [b, ite_eq_right hj] using ha j
  have hbeq (j : Fin (d + 1)) (y : Fin n → ℂ) (hy : y ≠ 0) :
      MvPolynomial.eval y (b j) = (P y).coeff j.val := by
    by_cases hj : j.val = d
    · rw [show b j = 1 from ite_eq_left hj, map_one, hj, ← (hP y hy).2]
      exact (hP y hy).1.coeff_natDegree.symm
    · simpa only [b, ite_eq_right hj] using heq j y hy
  have hbzero (j : Fin (d + 1)) :
      MvPolynomial.eval (0 : Fin n → ℂ) (b j) = if j.val = d then 1 else 0 := by
    by_cases hj : j.val = d
    · simp only [b, ite_eq_left hj, map_one]
    · rw [ite_eq_right hj, MvPolynomial.eval_zero]
      change AddMonoidAlgebra.coeff ((b j)) (0) = 0
      apply (hb j).coeff_eq_zero
      simp only [map_zero]
      have := j.isLt
      omega
  let F : MvPolynomial (Option (Fin n)) ℂ :=
    ∑ j : Fin (d + 1), MvPolynomial.rename some (b j) * MvPolynomial.X none ^ j.val
  refine ⟨F, ?_, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum Finset.univ _ d
    intro j _
    have hmul := ((hb j).rename_isHomogeneous (f := some)).mul
      ((MvPolynomial.isHomogeneous_X ℂ (none : Option (Fin n))).pow j.val)
    convert hmul using 1
    have := j.isLt
    omega
  · intro y hy z
    simp only [F, map_sum, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_X]
    change (∑ j : Fin (d + 1), MvPolynomial.eval y (b j) * z ^ j.val) = (P y).eval z
    simp_rw [hbeq _ y hy]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (P y).coeff j * z ^ j)]
    exact (eval_eq_sum_range' (show (P y).natDegree < d + 1 from by rw [(hP y hy).2]; omega) z).symm
  · intro z
    simp only [F, map_sum, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_X]
    change (∑ j : Fin (d + 1), MvPolynomial.eval 0 (b j) * z ^ j.val) = z ^ d
    rw [Finset.sum_eq_single (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1))]
    · rw [hbzero, ite_eq_left rfl, one_mul]
    · intro j _ hj
      have hjd : j.val ≠ d := fun h => hj (Fin.ext h)
      rw [hbzero, ite_eq_right hjd, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeFiberEquation.Constructions.Cone
