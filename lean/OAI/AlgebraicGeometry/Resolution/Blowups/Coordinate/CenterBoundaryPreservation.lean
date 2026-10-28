import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryChartExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.WithExceptional

/-! # Center Boundary Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryPreservation.Construction

noncomputable section

/-! Arbitrary exact coordinate presentations of the center preserve all included boundary labels. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Fintype σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_boundary_blowup_open_chart_of_coordinates
    (I : Ideal S) (C : Finset σ) (hI : I = Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C)
    (e : ι ↪ σ) (he : ∀ j, e j ∈ C) (w : ι → S) (hw : ∀ j, w j ∈ I)
    (hwe : ∀ j, algebraMap (MvPolynomial σ k) S (MvPolynomial.X (e j)) = w j)
    (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) p) := by
  subst I
  let eC : ι ↪ C := ⟨fun j => ⟨e j, he j⟩, fun _ _ h => e.injective (congrArg Subtype.val h)⟩
  have hfamily : Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw = BlowupBoundaryModel.Construction.coordinateBoundaryBlowupFamily C a eC := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        change ExceptionalIdeal.Construction.blowupChartRatio _ a ⟨w j, hw j⟩ =
          ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C (eC j))
        apply congrArg (ExceptionalIdeal.Construction.blowupChartRatio _ a)
        apply Subtype.ext
        exact (hwe j).symm
  rw [hfamily]
  exact BoundaryChartExistence.Construction.exists_coordinate_boundary_blowup_open_chart C a eC p

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryPreservation.Construction
