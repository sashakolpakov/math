import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.EtaleMonomialResolution
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameBlowupSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameCenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree

/-! # Monomial Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame.Construction

noncomputable section

/-! Actual dual center frames and original-base chart structures for monomial resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {σ k R : Type u} [DecidableEq σ] [Field k] [CommRing R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]

omit [DecidableEq σ] [Algebra.Etale (MvPolynomial σ k) R] [Algebra k R]
  [IsScalarTower k (MvPolynomial σ k) R] in
theorem etale_subset_coordinate_frame_span (C : Finset σ) :
    Ideal.span (Set.range (fun i : C => algebraMap (MvPolynomial σ k) R (MvPolynomial.X i.val))) =
      (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ k) R) := by
  rw [SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i.val, ⟨i.val, i.property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem etale_subset_coordinate_frame_dual (C : Finset σ) (i j : C) :
    DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i.val
      (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) = if i = j then 1 else 0 := by
  rw [DifferentialEquation.Construction.etaleRelativePartial_algebraMap, MvPolynomial.pderiv_X]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp [hv, hij]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Monomial.Construction.etaleSubsetCoordinatePolynomialAlgebra

omit [Algebra.Etale (MvPolynomial σ k) R] in
/-- The new monomial coordinates retain the original ground algebra on
the actual blowup chart, without replacing it by a competing instance. -/
theorem etale_subset_coordinate_chart_original_tower (C : Finset σ) (i : C) :
    IsScalarTower k (MvPolynomial σ k) (MonomialStep.Construction.etaleSubsetCoordinateChart (R := k) (S := R) C i) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change Blowup.Charts.Construction.blowupChartConstants _ _ (algebraMap k R c) = MonomialStep.Construction.etaleSubsetCoordinateMap (R := k) (S := R) C i
    (MvPolynomial.C c)
  rw [Monomial.Construction.etaleSubsetCoordinateMap_C]
  congr 1
  exact IsScalarTower.algebraMap_apply k (MvPolynomial σ k) R c

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame.Construction
