import OAI.Geometry.Nikodym.Beltrami.Distance
import OAI.Geometry.Nikodym.Beltrami.Volume
import OAI.Geometry.Nikodym.Chart.Geometry

noncomputable section
namespace OAI.Geometry.Nikodym

open Set _root_.MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Tubes formed using the actual infimum of Riemannian path lengths in the chart. -/
def beltramiTube (κ : ℝ) (S : Set E) (δ : ℝ) (I : Set E) : Set E :=
  {x | x ∈ S ∧ ∃ y ∈ I, beltramiChartEDist κ S x y < ENNReal.ofReal δ}

omit [CompleteSpace E] in
theorem beltramiTube_subset_euclidean {κ : ℝ} {S I : Set E} {δ : ℝ}
    (hsmall : ∀ x ∈ S, |κ| * ‖x‖^2 ≤ 1/2) :
    beltramiTube κ S δ I ⊆ metricTube (4*δ) I ∩ S := by
  rintro x ⟨hx,y,hy,hxy⟩
  refine ⟨⟨y,hy,?_⟩,hx⟩
  have hc : ENNReal.ofReal (dist x y / 4) ≤ beltramiChartEDist κ S x y := by
    have he : ENNReal.ofReal (dist x y / 4) = (1/4 : ℝ≥0∞) * edist x y := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),edist_dist]
      norm_num [div_eq_mul_inv,mul_comm]
    rw [he]
    exact beltramiChartEDist_lower hsmall x y
  have hd : dist x y / 4 < δ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp (hc.trans_lt hxy)
  linarith

omit [CompleteSpace E] in
theorem euclideanTube_subset_beltrami {κ : ℝ} {S I : Set E} {δ : ℝ}
    (hsmall : ∀ x ∈ S, |κ| * ‖x‖^2 ≤ 1/2) (hS : Convex ℝ S)
    (hI : I ⊆ S) (hδ : 0 < δ) :
    metricTube (δ/3) I ∩ S ⊆ beltramiTube κ S δ I := by
  rintro x ⟨⟨y,hy,hxy⟩,hx⟩
  refine ⟨hx,y,hy,?_⟩
  have hu := beltramiChartEDist_upper hsmall hS hx (hI hy)
  have he : (3 : ℝ≥0∞) * edist x y = ENNReal.ofReal (3*dist x y) := by
    rw [edist_dist,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [he] at hu
  exact hu.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith))

end OAI.Geometry.Nikodym
