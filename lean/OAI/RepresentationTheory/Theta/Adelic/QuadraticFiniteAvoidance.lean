import OAI.RepresentationTheory.Theta.Adelic.FinitePolynomialAvoidance
import OAI.RepresentationTheory.Theta.Adelic.QuadraticResidueRoots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Quadratic Finite Avoidance -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticFiniteAvoidance

noncomputable section

/-! More than twice the matrix rank many quadratic scalars with unit
pairwise differences suffice to avoid the spectrum, over every field. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.FinitePolynomialAvoidance OAI.RepresentationTheory.Theta.Adelic.QuadraticResidueRoots

variable {R k I : Type*} [CommRing R] [Field k] [Fintype I]

omit [Fintype I] in
theorem root_family_injective (f : R →+* k) (z : I → R)
    (hz : ∀ i j, i ≠ j → IsUnit (z i - z j)) : Function.Injective (fun i => f (z i)) := by
  intro i j h
  by_contra hij
  have hu := (hz i j hij).map f
  apply hu.ne_zero
  change f (z i) = f (z j) at h
  rw [map_sub, h, sub_self]

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem scalar_difference_map_det (f : R →+* k) (A : Matrix J J R) (z : R) :
    f (Matrix.scalar J z - A).det = (A.map f).charpoly.eval (f z) := by
  rw [f.map_det, Matrix.eval_charpoly]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.scalar_apply, h]

variable (d : k)

theorem quadratic_matrix_avoidance (A : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (z : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)
    (hz : ∀ i j, i ≠ j → IsUnit (z i - z j))
    (hcard : 2 * Fintype.card J < Fintype.card I) :
    ∃ i, IsUnit (Matrix.scalar J (z i) - A) := by
  by_cases hsq : IsSquare d
  · obtain ⟨r, hr⟩ := hsq
    have hr2 : r ^ 2 = d := by simpa only [pow_two] using hr.symm
    let p := (A.map (QuadraticResidueRoots.rootHom r hr2)).charpoly
    let q := (A.map (QuadraticResidueRoots.rootHom (-r) (by simpa using hr2))).charpoly
    obtain ⟨i, hp, hq⟩ := FinitePolynomialAvoidance.two_polynomial_avoidance p q
      (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero
      (fun i => QuadraticResidueRoots.rootHom r hr2 (z i)) (fun i => QuadraticResidueRoots.rootHom (-r) (by simpa using hr2) (z i))
      (root_family_injective _ z hz) (root_family_injective _ z hz) (by
        simpa only [p, q, Matrix.charpoly_natDegree_eq_dim, two_mul] using hcard)
    refine ⟨i, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
    apply QuadraticResidueRoots.rootHom_isUnit r hr2
    · rwa [scalar_difference_map_det]
    · rwa [scalar_difference_map_det]
  · let : Fact (∀ r : k, r ^ 2 ≠ d + 0 * r) := ⟨by
      intro r hr
      apply hsq
      exact ⟨r, by simpa only [pow_two, zero_mul, add_zero] using hr.symm⟩⟩
    have hinj : Function.Injective z := by
      intro i j he
      by_contra hij
      exact (hz i j hij).ne_zero (by rw [he, sub_self])
    obtain ⟨i, hi⟩ := FinitePolynomialAvoidance.polynomial_avoidance A.charpoly (Matrix.charpoly_monic _).ne_zero z hinj (by
      rw [Matrix.charpoly_natDegree_eq_dim]
      omega)
    refine ⟨i, (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)⟩
    rwa [← Matrix.eval_charpoly]

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticFiniteAvoidance
