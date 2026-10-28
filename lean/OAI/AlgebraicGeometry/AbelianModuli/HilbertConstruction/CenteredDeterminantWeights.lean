import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumCoordinateProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantBlockDegrees
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDeterminantSeparation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.DimensionalPositiveInterior

/-! # Centered Determinant Weights -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CenteredDeterminantWeights

noncomputable section

/-! The centered incidence vectors of all nonvanishing determinants
have zero in the interior of their convex hull for a sparse configuration. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {r m : ℕ}

def determinantIncidenceVector (σ : Fin r → Fin m) : Fin m → ℝ :=
  fun i => DeterminantBlockDegrees.labeledDeterminantWeight σ i

theorem determinantIncidenceVector_pairing (σ : Fin r → Fin m) (a : Fin m → ℝ) :
    ∑ i, determinantIncidenceVector σ i * a i = ∑ j, a (σ j) := by
  simp only [determinantIncidenceVector, DeterminantBlockDegrees.labeledDeterminantWeight, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

def nonzeroDeterminantLabels (v : Fin m → Fin r → K) :=
  {σ : Fin r → Fin m // LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0}

instance nonzeroDeterminantLabels_fintype (v : Fin m → Fin r → K) :
    Fintype (nonzeroDeterminantLabels v) :=
  inferInstanceAs (Fintype {σ : Fin r → Fin m // LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0})

theorem nonzeroDeterminantLabels_nonempty (v : Fin m → Fin r → K)
    (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    Nonempty (nonzeroDeterminantLabels v) := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by intro h; have hh := congrArg Fin.val h; change 0 = 1 at hh; omega
  let a : Fin m → ℝ := Pi.single i₀ 1 - Pi.single i₁ 1
  have ha : ∑ i, a i = 0 := by simp [a, Pi.single_apply]
  have hne : a ≠ 0 := by
    intro h
    have hh := congrFun h i₀
    simp [a, hi] at hh
  obtain ⟨σ, hσ, _⟩ := SparseDeterminantSeparation.sparseConfiguration_determinant_separates_zeroSum_weight v hv hr hs a ha hne
  exact ⟨⟨σ, hσ⟩⟩

def centeredDeterminantWeights (v : Fin m → Fin r → K) (hm : 0 < m) :
    nonzeroDeterminantLabels v → ZeroSumCoordinateProjection.zeroSumCoordinates m :=
  fun σ => ZeroSumCoordinateProjection.zeroSumProjectionTo hm (determinantIncidenceVector σ.val)

theorem centeredDeterminantWeights_positive_functional (v : Fin m → Fin r → K)
    (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 0 < m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m)
    (f : StrongDual ℝ (ZeroSumCoordinateProjection.zeroSumCoordinates m)) (hf : f ≠ 0) :
    ∃ σ, 0 < f (centeredDeterminantWeights v hm σ) := by
  have hfl : f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    ext x
    exact congrArg (fun g : ZeroSumCoordinateProjection.zeroSumCoordinates m →ₗ[ℝ] ℝ => g x) h
  let a := ZeroSumCoordinateProjection.zeroSumFunctionalWeights hm f.toLinearMap
  obtain ⟨σ, hσ, hsum⟩ := SparseDeterminantSeparation.sparseConfiguration_determinant_separates_zeroSum_weight v hv hr hs a
    (ZeroSumCoordinateProjection.zeroSumFunctionalWeights_sum hm _) (ZeroSumCoordinateProjection.zeroSumFunctionalWeights_ne_zero hm _ hfl)
  refine ⟨⟨σ, hσ⟩, ?_⟩
  change 0 < f.toLinearMap (ZeroSumCoordinateProjection.zeroSumProjectionTo hm (determinantIncidenceVector σ))
  rw [ZeroSumCoordinateProjection.zeroSumFunctionalWeights_eval, determinantIncidenceVector_pairing]
  exact hsum

theorem centeredDeterminantWeights_zero_interior (v : Fin m → Fin r → K)
    (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    (0 : ZeroSumCoordinateProjection.zeroSumCoordinates m) ∈
      interior (convexHull ℝ (Set.range (centeredDeterminantWeights v (by omega)))) := by
  let : Nonempty (nonzeroDeterminantLabels v) := nonzeroDeterminantLabels_nonempty v hv hr hm hs
  exact Finite.DimensionalPositiveInterior.zero_mem_interior_convexHull_of_all_positive_functionals _
    (centeredDeterminantWeights_positive_functional v hv hr (by omega) hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CenteredDeterminantWeights
