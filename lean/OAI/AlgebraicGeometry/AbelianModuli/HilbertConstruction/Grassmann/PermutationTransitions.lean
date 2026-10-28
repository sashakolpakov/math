import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapDeterminants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.PermutationCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.SubmoduleBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartInverses

/-! # Permutation Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! Permuted Grassmannian chart transitions commute with arbitrary scalar extension. -/

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] {k l : ℕ}

/-- Validity of the alternate frame is stable under every coefficient-ring map. -/
theorem Charts.GrassmannChart.overlap_map (φ : R →+* B) (c : Charts.GrassmannChart R (Fin l → R) k)
    (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap)) :
    Function.Bijective ((Charts.grassmannQuotientChartEquiv (Charts.GrassmannChart.map φ c)).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation B τ).toLinearMap) := by
  apply (Chart.OverlapDeterminants.quotientChart_overlap_iff _ τ).mpr
  change IsUnit (Chart.OverlapMatrices.chartOverlapMatrix (PolynomialCoordinates.grassmannChartMatrixEquiv (Charts.GrassmannChart.map φ c)) τ).det
  rw [Charts.GrassmannChart.map_matrix]
  exact (Chart.OverlapMatrices.chartOverlapDet_naturality φ (PolynomialCoordinates.grassmannChartMatrixEquiv c) τ) ▸
    ((Chart.OverlapDeterminants.quotientChart_overlap_iff _ τ).mp h).map φ

/-- The same quotient in the chart obtained by permuting its ambient coordinates. -/
def Charts.GrassmannChart.permute (c : Charts.GrassmannChart R (Fin l → R) k) (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap)) : Charts.GrassmannChart R (Fin l → R) k :=
  Charts.grassmannQuotientChartEquiv.symm ((Charts.grassmannQuotientChartEquiv c).transition
    (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap h)

/-- The transition changes the defining submodule by the actual inverse image. -/
theorem Charts.GrassmannChart.permute_kernel (c : Charts.GrassmannChart R (Fin l → R) k) (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap)) :
    (Charts.GrassmannChart.permute c τ h).val.toSubmodule = c.val.toSubmodule.comap (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap :=
  (Charts.grassmannQuotientChartEquiv c).transition_kernel _ h

/-- The transition is natural for scalar extension of the actual quotient submodules. -/
theorem Charts.GrassmannChart.permute_naturality (φ : R →+* B) (c : Charts.GrassmannChart R (Fin l → R) k)
    (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap)) :
    Charts.GrassmannChart.map φ (Charts.GrassmannChart.permute c τ h) = Charts.GrassmannChart.permute (Charts.GrassmannChart.map φ c) τ (Charts.GrassmannChart.overlap_map φ c τ h) := by
  apply Subtype.ext
  apply Module.Grassmannian.ext
  rw [Charts.GrassmannChart.map_kernel, Charts.GrassmannChart.permute_kernel, Charts.GrassmannChart.permute_kernel, Charts.GrassmannChart.map_kernel]
  exact Chart.SubmoduleBaseChange.span_image_comap_equiv (Matrix.ChartBaseChange.chartPairMap φ k l) (Chart.CoordinatePermutations.chartCoordinatePermutation R τ)
    (Chart.CoordinatePermutations.chartCoordinatePermutation B τ) (Chart.CoordinatePermutations.chartCoordinatePermutation_naturality φ τ) c.val.toSubmodule

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
