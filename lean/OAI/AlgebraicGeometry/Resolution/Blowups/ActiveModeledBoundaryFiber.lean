import OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicBoundaryFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ExtendUnitLabels

/-! # Active Modeled Boundary Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryFiber.Construction

noncomputable section

/-! Coefficient hypersurfaces at arbitrary primes retain the full original boundary. -/

universe u v

/-- Isolate the active labels, construct maximal contact, and restore
every inactive label as its actual invertible equation. Both the ambient
neighborhood and its coefficient hypersurface retain the full family. -/
theorem exists_active_modeled_boundary_fiber
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] (w : ι → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (J : Ideal R) (n : ℕ) (p : PrimeSpectrum R)
    (hJ : J.map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (n + 1))
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤) :
    ∃ C : ActiveModeledBoundaryChart.Construction.ActiveModeledBoundaryOpenChart k R w J (n + 1) p,
      let A := Localization.Away C.denominator
      ∃ (z : A) (E : Derivation k A A) (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z),
        z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R A)) n ∧
        z ∈ C.point.asIdeal ∧ E z ∉ C.point.asIdeal ∧
        E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
          (fun j : C.active => algebraMap R A (w j.val)) ∧
        Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Localization.Away f) ι
          (fun j => algebraMap R (Localization.Away f) (w j))) ∧
        Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryModel k
          (Localization.Away f ⧸ Ideal.span {algebraMap A (Localization.Away f) z}) ι
          (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap A (Localization.Away f) z})
            (algebraMap R (Localization.Away f) (w j)))) ∧
        ∃ η : Localization.Away f →+* C.point.asIdeal.ResidueField,
          ∀ r : A, η (algebraMap A (Localization.Away f) r) =
            algebraMap A C.point.asIdeal.ResidueField r := by
  obtain ⟨C⟩ := ActiveModeledBoundaryChart.Construction.exists_active_modeled_boundary_open_chart R w M J (n + 1) p hbound
  let A := Localization.Away C.denominator
  obtain ⟨z, E, f, hz, hzq, hEz, hE, ⟨N⟩, ⟨B⟩, η, hη⟩ :=
    Modeled.LogarithmicBoundaryFiber.Construction.exists_modeled_logarithmic_boundary_fiber C.model C.point.asIdeal C.active_equations_mem
      (J.map (algebraMap R A)) n (C.local_order hJ) C.logarithmicBound
  let U := Localization.Away f
  let Z : Ideal U := Ideal.span {algebraMap A U z}
  have hu (j : ι) (hj : j ∉ C.active) : IsUnit (algebraMap R U (w j)) := by
    rw [IsScalarTower.algebraMap_apply R A U]
    exact (C.inactive_units j hj).map (algebraMap A U)
  have hN : Etale.BoundaryModel.Construction.EtaleBoundaryModel k U C.active
      (fun j => algebraMap R U (w j.val)) := by
    exact N
  have hB : Etale.BoundaryModel.Construction.EtaleBoundaryModel k (U ⧸ Z) C.active
      (fun j => Ideal.Quotient.mk Z (algebraMap R U (w j.val))) := by
    exact B
  let N' := Etale.BoundaryModel.Construction.EtaleBoundaryModel.extendUnitLabels (fun j => algebraMap R U (w j)) C.active hN hu
  let B' := Etale.BoundaryModel.Construction.EtaleBoundaryModel.extendUnitLabels
    (fun j => Ideal.Quotient.mk Z (algebraMap R U (w j))) C.active hB
    (fun j hj => (hu j hj).map (Ideal.Quotient.mk Z))
  exact ⟨C, z, E, f, hz, hzq, hEz, hE, ⟨N'⟩, ⟨B'⟩, η, hη⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryFiber.Construction
