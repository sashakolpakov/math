import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Form Localization Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizationCover.ProjectiveCech

noncomputable section

/-! On localization at a homogeneous linear form, the projective coordinate images generate the unit ideal. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type u} (R : Type v) [CommRing R]

theorem linearForm_mem_span_variables (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1) :
    l ∈ Ideal.span (Set.range (X (R := R) : σ → MvPolynomial σ R)) := by
  have hle : Submodule.span R (Set.range (X (R := R) : σ → MvPolynomial σ R)) ≤
      (Ideal.span (Set.range (X (R := R) : σ → MvPolynomial σ R))).restrictScalars R :=
    Submodule.span_le.mpr (fun _ hx => Ideal.subset_span hx)
  apply hle
  rw [← homogeneousSubmodule_one_eq_span_X]
  exact hl

theorem linearFormLocalization_coordinates_span_top (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1) :
    Ideal.span (Set.range (fun i : σ => algebraMap (MvPolynomial σ R) (Localization.Away l) (X i))) = ⊤ := by
  have hmem := Ideal.mem_map_of_mem (algebraMap (MvPolynomial σ R) (Localization.Away l))
    (linearForm_mem_span_variables R l hl)
  rw [Ideal.map_span, ← Set.range_comp] at hmem
  exact Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit l)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizationCover.ProjectiveCech
