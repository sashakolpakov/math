import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedCoordinateSubspaceCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateComparisonPrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ComparisonProtectedChart

/-! # Protected Pattern Program Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternProgramExistence.Construction

noncomputable section

/-! A nonzero global ideal has a terminating actual program equipped with protected chart patterns on any compact smooth part of its carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_control_one_with_protected_patterns
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (O : X.Opens) [Nonempty O] [CompactSpace O]
    [Smooth ((J.comap O.ι).subschemeι ≫ (O.ι ≫ f))] :
    ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K), K = ⊤ ∧ Nonempty (ProtectedPatternChart.Construction.ProtectedPatternProgramCover P O) := by
  obtain ⟨ι, hι, x, C, hx, hO, hcover⟩ := ProtectedCoordinateSubspaceCover.Construction.exists_finite_protected_coordinate_subspace_cover f J hJ O
  let : Fintype ι := hι
  obtain ⟨Y, g, K, P, ht, hprogram⟩ := Finite.CoordinateComparisonPrograms.Construction.exists_global_control_one_with_coordinate_comparisons f J hJ x C
  let A (i : ι) := (Classical.choice (hprogram i)).toProtectedChart O (hx i) (hO i)
  exact ⟨Y, g, K, P, ht, ⟨{ indices := ι, chart := A, cover := hcover }⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternProgramExistence.Construction
