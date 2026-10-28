import OAI.RepresentationTheory.Theta.Adelic.QuadraticFiniteAvoidance
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Quadratic Local Ring Avoidance -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalRingAvoidance

noncomputable section

/-! The finite spectral avoidance theorem over a quadratic algebra
lifts from the residue field to every commutative local base ring. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.QuadraticFiniteAvoidance
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] (d : R)

theorem quadratic_residue_isUnit_iff (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) :
    IsUnit (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d z) ↔ IsUnit z := by
  constructor
  · intro hz
    have hn := hz.map QuadraticAlgebra.norm
    rw [Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_norm] at hn
    exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      ((residue_ne_zero_iff_isUnit _).mp hn.ne_zero)
  · exact fun hz => hz.map (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d)

theorem matrix_residue_isUnit_iff {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) :
    IsUnit (A.map (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d)) ↔ IsUnit A := by
  simp only [Matrix.isUnit_iff_isUnit_det]
  have he : Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d A.det =
      (A.map (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d)).det :=
    (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d).map_det A
  rw [← he, quadratic_residue_isUnit_iff]

theorem quadratic_local_ring_avoidance {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) (z : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)
    (hz : ∀ i j, i ≠ j → IsUnit (z i - z j))
    (hcard : 2 * Fintype.card J < Fintype.card I) :
    ∃ i, IsUnit (Matrix.scalar J (z i) - A) := by
  let f := Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (residue R) d
  have hdif : ∀ i j, i ≠ j → IsUnit (f (z i) - f (z j)) := by
    intro i j hij
    exact (f.map_sub (z i) (z j)) ▸ ((hz i j hij).map f)
  obtain ⟨i, hi⟩ := QuadraticFiniteAvoidance.quadratic_matrix_avoidance (residue R d) (A.map f) (fun i => f (z i)) hdif hcard
  refine ⟨i, (matrix_residue_isUnit_iff d _).mp ?_⟩
  have he : (Matrix.scalar J (z i) - A).map f = Matrix.scalar J (f (z i)) - A.map f := by
    apply Matrix.ext
    intro j k
    by_cases h : j = k <;> simp [Matrix.map_apply, Matrix.scalar_apply, h]
  rw [he]
  exact hi

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalRingAvoidance
