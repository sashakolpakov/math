import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransverseEquation
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterPivot
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame

/-! # Transverse Contained Center Pivot -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterPivot.Construction

noncomputable section

/-! A hypersurface in a coordinate center has a pivot preserving every active boundary coordinate. -/

universe u

/-- A transverse equation contained in the center can replace a center
coordinate outside the whole active boundary. The actual linear-combination
coefficient and the coordinate derivative both avoid the original prime. -/
theorem exists_transverse_contained_center_pivot
    {σ k R : Type u} [Field k] [CommRing R] [Fintype σ] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]
    (C B : Finset σ) (q : Ideal R)
    (hC : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C ≤ q)
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈ q)
    (z : R) (hz : z ∈ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C)
    (E : Derivation k R R)
    (hE : ∀ i ∈ B, E (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)})
    (hEz : E z ∉ q) :
    ∃ (i : C) (c : C → R), i.val ∉ B ∧
      (∑ j, c j * algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) = z ∧
      c i ∉ q ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i.val z ∉ q := by
  classical
  obtain ⟨i, hiB, hi⟩ := Relative.LogarithmicTransverseEquation.Construction.relative_logarithmic_derivative_detects_transverse_direction B q hB E hE z hEz
  have hiC : i ∈ C := by
    by_contra h
    apply hi
    apply hC
    change (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i).restrictScalars ℤ z ∈ _
    rw [Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial_restrictScalars]
    exact Coordinate.CenterBoundaryContainment.Construction.etale_outside_coordinate_derivation_preserves_center C i h hz
  let g : C → R := fun j => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)
  let D : C → Derivation k R R := fun j => Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j.val
  have hgen : Ideal.span (Set.range g) = Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C :=
    Blowups.Etale.MonomialFrame.Construction.etale_subset_coordinate_frame_span C
  have hz' : z ∈ Ideal.span (Set.range g) := hgen.symm ▸ hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz'
  have hmod := Boundary.CenterPivot.Construction.dual_center_derivative_mod_ideal g D (Blowups.Etale.MonomialFrame.Construction.etale_subset_coordinate_frame_dual C)
    q (fun j => hC (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C j).property) c ⟨i, hiC⟩
  rw [hc] at hmod
  have hci : c ⟨i, hiC⟩ ∉ q := by
    intro h
    apply hi
    have he := q.add_mem hmod h
    simpa only [sub_add_cancel] using he
  exact ⟨⟨i, hiC⟩, c, hiB, hc, hci, hi⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterPivot.Construction
