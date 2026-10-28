import OAI.AlgebraicGeometry.Resolution.Blowups.FramedBoundaryClearance
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame

/-! # Center Pivot -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterPivot.Construction

noncomputable section

/-! A smooth boundary equation inside a framed center admits a nonvanishing center pivot. -/

universe u

variable {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Fintype ι] [DecidableEq ι]

/-- At points of the center, differentiating a linear combination in a
dual center frame recovers its coefficient modulo the center prime. -/
theorem dual_center_derivative_mod_ideal
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (q : Ideal R) (hg : ∀ i, g i ∈ q) (c : ι → R) (i : ι) :
    D i (∑ j, c j * g j) - c i ∈ q := by
  have hder : D i (∑ j, c j * g j) = c i + ∑ j, g j * D i (c j) := by
    simp [map_sum, Derivation.leibniz, hD, smul_eq_mul, Finset.sum_add_distrib]
  rw [hder, add_sub_cancel_left]
  exact q.sum_mem (fun j _ => q.mul_mem_right _ (hg j))

/-- An equation in the center whose derivative is nonzero at the point
has a center coefficient and corresponding dual derivative both nonzero
there. These explicit coefficients support a local frame replacement. -/
theorem exists_boundary_center_pivot
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (z : R) (hz : z ∈ Ideal.span (Set.range g))
    (E : Derivation k R R) (q : Ideal R) (hg : ∀ i, g i ∈ q) (hEz : E z ∉ q) :
    ∃ (c : ι → R) (i : ι), (∑ j, c j * g j) = z ∧ c i ∉ q ∧ D i z ∉ q := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
  obtain ⟨i, hi⟩ : ∃ i, c i ∉ q := by
    by_contra! hcoeff
    apply hEz
    rw [← hc, map_sum]
    apply q.sum_mem
    intro j _
    rw [Derivation.leibniz]
    change c j * E (g j) + g j * E (c j) ∈ q
    exact q.add_mem (q.mul_mem_right _ (hcoeff j)) (q.mul_mem_right _ (hg j))
  refine ⟨c, i, hc, hi, ?_⟩
  have hmod := dual_center_derivative_mod_ideal g D hD q hg c i
  rw [hc] at hmod
  intro hDz
  apply hi
  have h := q.sub_mem hDz hmod
  convert h using 1
  abel

/-- If the detecting derivative annihilates already retained generators,
the pivot can be chosen outside their index set. Thus a later boundary
replacement need not disturb any boundary coordinate retained earlier. -/
theorem exists_boundary_center_pivot_outside
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (z : R) (hz : z ∈ Ideal.span (Set.range g))
    (E : Derivation k R R) (q : Ideal R) (hg : ∀ i, g i ∈ q) (hEz : E z ∉ q)
    (B : Finset ι) (hEB : ∀ i ∈ B, E (g i) = 0) :
    ∃ (c : ι → R) (i : ι), i ∉ B ∧ (∑ j, c j * g j) = z ∧ c i ∉ q ∧ D i z ∉ q := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
  obtain ⟨i, hiB, hi⟩ : ∃ i ∉ B, c i ∉ q := by
    by_contra! hcoeff
    apply hEz
    rw [← hc, map_sum]
    apply q.sum_mem
    intro j _
    rw [Derivation.leibniz]
    change c j * E (g j) + g j * E (c j) ∈ q
    apply q.add_mem
    · by_cases hjB : j ∈ B
      · rw [hEB j hjB, mul_zero]
        exact q.zero_mem
      · exact q.mul_mem_right _ (hcoeff j hjB)
    · exact q.mul_mem_right _ (hg j)
  refine ⟨c, i, hiB, hc, hi, ?_⟩
  have hmod := dual_center_derivative_mod_ideal g D hD q hg c i
  rw [hc] at hmod
  intro hDz
  apply hi
  have h := q.sub_mem hDz hmod
  convert h using 1
  abel

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterPivot.Construction
