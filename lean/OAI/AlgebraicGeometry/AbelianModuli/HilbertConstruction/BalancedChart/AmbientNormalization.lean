import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEmbedding

/-! # Ambient Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientNormalization

noncomputable section

/-! The chart coordinates, embedded in the ambient localization, are
obtained by one linear change of coordinates and invertible point scalings. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}

theorem balancedChartAmbientVectors_aeval (a : (Fin r → Fin m) → ℕ)
    (p : MvPolynomial (Fin m × Fin r) R) :
    MvPolynomial.aeval (fun jk : Fin m × Fin r => AmbientFrame.balancedChartAmbientVectors R a jk.1 jk.2) p =
      algebraMap (MvPolynomial (Fin m × Fin r) R) (AmbientFrame.balancedChartAmbientRing R a) p := by
  let φ := IsScalarTower.toAlgHom R (MvPolynomial (Fin m × Fin r) R) (AmbientFrame.balancedChartAmbientRing R a)
  have h : MvPolynomial.aeval (fun jk : Fin m × Fin r => AmbientFrame.balancedChartAmbientVectors R a jk.1 jk.2) = φ := by
    ext jk
    exact MvPolynomial.aeval_X _ jk
  exact congrArg (fun f : MvPolynomial (Fin m × Fin r) R →ₐ[R] AmbientFrame.balancedChartAmbientRing R a => f p) h

theorem balancedFrameChartVectors_ambient_rescale
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a) :
    ∃ s : Fin m → AmbientFrame.balancedChartAmbientRing R a, (∀ z, IsUnit (s z)) ∧ ∀ z k,
      Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m)
          (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
          (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) =
        s z * DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (AmbientFrame.balancedChartAmbientRing R a) (Fin r))
          (fun j => AmbientFrame.balancedChartAmbientVectors R a (σ j)) (AmbientFrame.balancedChartAmbientVectors R a e)
          (AmbientFrame.balancedChartAmbientVectors R a z) k := by
  let v := AmbientFrame.balancedChartAmbientVectors R a
  let T := DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (AmbientFrame.balancedChartAmbientRing R a) (Fin r))
    (fun j => v (σ j)) (v e)
  have hu (z : Fin m) : IsUnit (T (v z) (c z)) := by
    apply AmbientFrame.balancedChartAmbientVectors_coordinate_isUnit R σ e z (c z) a
    intro τ
    calc
      Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) τ ≤ C z τ + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) τ :=
        Nat.le_add_left _ _
      _ = a τ := congrFun (hC z) τ
  let s : Fin m → AmbientFrame.balancedChartAmbientRing R a := fun z => ↑(hu z).unit⁻¹
  refine ⟨s, fun z => Units.isUnit _, ?_⟩
  intro z k
  apply (hu z).mul_right_cancel
  calc
    _ = T (v z) k := by
      have h := AmbientFrame.balancedFrameChartCoordinate_ambient_crossMultiply R i σ e z (c z) k a (C z) ha (hC z)
      simp only [Frame.CoordinateMonomials.frameCoordinateExponent_linearMap] at h
      exact h
    _ = (s z * T (v z) (c z)) * T (v z) k := by rw [(hu z).val_inv_mul, one_mul]
    _ = (s z * T (v z) k) * T (v z) (c z) := by ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientNormalization
