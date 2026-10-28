import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.CoordinatePermutations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.FrameDeterminants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartTransitions

/-! # Overlap Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMatrices

noncomputable section

/-! The square matrices defining overlaps of permuted Grassmannian quotient charts. -/

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] {k l : ℕ}

/-- The normalized projection associated with a rectangular matrix. -/
def chartMatrixProjection (M : Matrix (Fin k) (Fin l) R) :
    ((Fin k → R) × (Fin l → R)) →ₗ[R] (Fin k → R) := LinearMap.id.coprod M.mulVecLin

/-- The new first block after an ambient coordinate permutation. -/
def chartOverlapMatrix (M : Matrix (Fin k) (Fin l) R) (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    Matrix (Fin k) (Fin k) R :=
  LinearMap.toMatrix' ((chartMatrixProjection M).comp
    ((CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap.comp (LinearMap.inl R (Fin k → R) (Fin l → R))))

theorem chartMatrixProjection_naturality (φ : R →+* B) (M : Matrix (Fin k) (Fin l) R)
    (x : (Fin k → R) × (Fin l → R)) :
    HilbertConstruction.Matrix.ChartBaseChange.chartVectorMap φ k (chartMatrixProjection M x) =
      chartMatrixProjection (M.map φ) (HilbertConstruction.Matrix.ChartBaseChange.chartPairMap φ k l x) := by
  ext i
  change φ (x.1 i + (M.mulVec x.2) i) = φ (x.1 i) +
    ((M.map φ).mulVec (fun j => φ (x.2 j))) i
  rw [map_add, RingHom.map_mulVec]
  rfl

theorem chartVectorMap_single (φ : R →+* B) (n : ℕ) (j : Fin n) :
    HilbertConstruction.Matrix.ChartBaseChange.chartVectorMap φ n (Pi.single j 1) = Pi.single j 1 := by
  ext i
  simp [HilbertConstruction.Matrix.ChartBaseChange.chartVectorMap, Pi.single_apply, apply_ite]
  split_ifs <;> simp_all

/-- Overlap matrices are compatible with every map of coefficient rings. -/
theorem chartOverlapMatrix_naturality (φ : R →+* B) (M : Matrix (Fin k) (Fin l) R)
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    (chartOverlapMatrix M τ).map φ = chartOverlapMatrix (M.map φ) τ := by
  ext i j
  have hi : HilbertConstruction.Matrix.ChartBaseChange.chartPairMap φ k l (Pi.single j 1, 0) = (Pi.single j 1, 0) := by
    apply Prod.ext
    · exact chartVectorMap_single φ k j
    · exact map_zero (HilbertConstruction.Matrix.ChartBaseChange.chartVectorMap φ l)
  have hp := chartMatrixProjection_naturality φ M
    (CoordinatePermutations.chartCoordinatePermutation R τ (Pi.single j 1, 0))
  rw [CoordinatePermutations.chartCoordinatePermutation_naturality, hi] at hp
  exact congrFun hp i

/-- The determinant defining an overlap also commutes with scalar change. -/
theorem chartOverlapDet_naturality (φ : R →+* B) (M : Matrix (Fin k) (Fin l) R)
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    φ (chartOverlapMatrix M τ).det = (chartOverlapMatrix (M.map φ) τ).det := by
  exact (φ.map_det _).trans (congrArg Matrix.det (chartOverlapMatrix_naturality φ M τ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMatrices
