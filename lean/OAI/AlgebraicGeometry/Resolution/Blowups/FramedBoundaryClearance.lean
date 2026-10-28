import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceBoundaryPhase

/-! # Framed Boundary Clearance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FramedBoundaryClearance.Construction

noncomputable section

/-! Boundary phases for actual nonempty intersections in a dual coordinate frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Every nonempty selected boundary intersection has first relative
differential ideal equal to the unit ideal, directly from its dual frame. -/
theorem boundaryIntersection_relative_first_bound (k : Type u) {R ι : Type u}
    [CommRing k] [CommRing R] [Algebra k R] [DecidableEq ι]
    (w : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0)
    (B : Finset ι) (hB : B.Nonempty) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B) 1 = ⊤ := by
  obtain ⟨i, hi⟩ := hB
  have hwi : w i ∈ Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B := Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hmem := Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B) (D i) hwi
  rw [hD, ite_eq_left rfl] at hmem
  exact Ideal.eq_top_of_isUnit_mem _ hmem isUnit_one

/-- A selected nonempty boundary intersection on a smooth affine surface
can be cleared from any positive-control order locus by a finite actual
phase. Its first differential bound is derived from the boundary frame. -/
theorem exists_smooth_surface_framed_boundary_clearance
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {ι : Type u} [DecidableEq ι]
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    (hd : ringKrullDim R ≤ 2) (w : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0)
    (B : Finset ι) (hB : B.Nonempty) (J : Ideal R) (m : ℕ) (hm : 0 < m) :
    Nonempty (Boundary.ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B)) :=
  Blowups.Smooth.SurfaceBoundaryPhase.Construction.exists_smooth_surface_boundary_control_phase k R hd J _ m hm
    (boundaryIntersection_relative_first_bound k w D hD B hB)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FramedBoundaryClearance.Construction
