import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyLength
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Complex Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ComplexEuler

noncomputable section

/-! Euler characteristic for a finitely supported complex of finite-length
modules with any complex shape. Opposite weights on adjacent degrees cancel
the actual boundary images. This also applies to pages of a spectral sequence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

variable (R : Type) [CommRing R] {ι : Type} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c)

def boundary (i j : ι) : ℚ := ExactLength.rationalLength R (.of R (LinearMap.range (K.d i j).hom))

theorem boundary_zero (i j : ι) (h : K.d i j = 0) : boundary R K i j = 0 :=
  ExactLength.rationalLength_range_of_zero R _ h

theorem incoming (F : Finset ι) (hout : ∀ i, i ∉ F → IsZero (K.X i)) (i : ι) :
    (∑ j ∈ F, boundary R K j i) = boundary R K (c.prev i) i := by
  apply Finset.sum_eq_single (c.prev i)
  · intro j _ hj
    apply boundary_zero
    apply K.shape
    intro h
    exact hj (c.prev_eq' h).symm
  · intro hi
    exact boundary_zero R K _ _ ((hout _ hi).eq_of_src _ _)

theorem outgoing (F : Finset ι) (hout : ∀ i, i ∉ F → IsZero (K.X i)) (i : ι) :
    (∑ j ∈ F, boundary R K i j) = boundary R K i (c.next i) := by
  apply Finset.sum_eq_single (c.next i)
  · intro j _ hj
    apply boundary_zero
    apply K.shape
    intro h
    exact hj (c.next_eq' h).symm
  · intro hi
    exact boundary_zero R K _ _ ((hout _ hi).eq_of_tgt _ _)

theorem degree (F : Finset ι) (hout : ∀ i, i ∉ F → IsZero (K.X i))
    (i : ι) (hi : Module.length R (K.X i) ≠ ⊤) :
    ExactLength.rationalLength R (K.X i) = ExactLength.rationalLength R (K.homology i) +
      (∑ j ∈ F, boundary R K j i) + ∑ j ∈ F, boundary R K i j := by
  rw [incoming R K F hout, outgoing R K F hout]
  exact HomologyLength.middle_length R (K.sc i) hi

theorem boundaries_cancel (F : Finset ι) (w : ι → ℚ)
    (hw : ∀ i j, c.Rel i j → w i + w j = 0) :
    (∑ i ∈ F, w i * ∑ j ∈ F, boundary R K j i) +
      (∑ i ∈ F, w i * ∑ j ∈ F, boundary R K i j) = 0 := by
  simp_rw [Finset.mul_sum]
  have he : (∑ i ∈ F, ∑ j ∈ F, w i * boundary R K j i) =
      ∑ i ∈ F, ∑ j ∈ F, w j * boundary R K i j := Finset.sum_comm
  rw [he, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : c.Rel i j
  · have h := hw i j hij
    calc
      w j * boundary R K i j + w i * boundary R K i j =
          (w i + w j) * boundary R K i j := by ring
      _ = 0 := by rw [h, zero_mul]
  · rw [boundary_zero R K i j (K.shape i j hij), mul_zero, mul_zero, add_zero]

theorem homology_euler (F : Finset ι) (hout : ∀ i, i ∉ F → IsZero (K.X i))
    (hlen : ∀ i ∈ F, Module.length R (K.X i) ≠ ⊤)
    (w : ι → ℚ) (hw : ∀ i j, c.Rel i j → w i + w j = 0) :
    (∑ i ∈ F, w i * ExactLength.rationalLength R (K.homology i)) =
      ∑ i ∈ F, w i * ExactLength.rationalLength R (K.X i) := by
  have hdegree : (∑ i ∈ F, w i * ExactLength.rationalLength R (K.X i)) =
      (∑ i ∈ F, w i * ExactLength.rationalLength R (K.homology i)) +
        ((∑ i ∈ F, w i * ∑ j ∈ F, boundary R K j i) +
          ∑ i ∈ F, w i * ∑ j ∈ F, boundary R K i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [degree R K F hout i (hlen i hi)]
    ring
  rw [boundaries_cancel R K F w hw, add_zero] at hdegree
  exact hdegree.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ComplexEuler
