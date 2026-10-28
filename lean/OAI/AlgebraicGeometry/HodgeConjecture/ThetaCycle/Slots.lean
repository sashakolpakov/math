import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SparseSpanning
import OAI.RepresentationTheory.Theta.Kernel.Calculus

/-! # Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots.CM

noncomputable section

section

/-! Construct two genuine finite theta inputs with nonzero wedge value.
The wedge is the determinant of the actual one-form coefficients. -/

open scoped Classical ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d d₀ d₁ : Gal(K/ℚ) → Bool}

def sourceThetaCoordinates (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) : Fin 2 → ℂ :=
  SparseSpanning.CM.jacobiCoefficients (Fin 2) (Projection.CM.sourceThetaCovector K L φ z)

theorem source_theta_coordinates_span (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Submodule.span ℂ (Set.range (fun φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places) =>
      sourceThetaCoordinates K L φ z)) = ⊤ := by
  change Submodule.span ℂ (Set.range (fun φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places) =>
    SparseSpanning.CM.jacobiCoefficients (Fin 2) (Projection.CM.sourceThetaCovector K L φ z))) = ⊤
  rw [Set.range_comp' (SparseSpanning.CM.jacobiCoefficients (Fin 2)), Submodule.span_image,
    SparseSpanning.CM.source_theta_covector_span K L z hz, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (SparseSpanning.CM.jacobi_coefficients_surjective (Fin 2))

def sourceWedgeCoefficient (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient (sourceThetaCoordinates K L₀ φ z)
    (sourceThetaCoordinates K L₁ ψ z)

theorem exists_source_wedge_nonzero
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    ∃ φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places), sourceWedgeCoefficient K L₀ L₁ φ ψ z ≠ 0 :=
  RepresentationTheory.Theta.Kernel.Calculus.exists_wedge_ne_zero
    (fun φ => sourceThetaCoordinates K L₀ φ z) (fun ψ => sourceThetaCoordinates K L₁ ψ z)
    (source_theta_coordinates_span K L₀ z hz) (source_theta_coordinates_span K L₁ z hz)

omit [IsGalois ℚ K] in
theorem source_wedge_smooth
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ContDiffOn ℝ ∞ (sourceWedgeCoefficient K L₀ L₁ φ ψ) B.domain := by
  have h₀ := Projection.CM.source_theta_covector_smooth K L₀ φ
  have h₁ := Projection.CM.source_theta_covector_smooth K L₁ ψ
  have he₀ (v : HeckeCycles.GeometricSource.CM.BallChart) : ContDiffOn ℝ ∞ (fun z => Projection.CM.sourceThetaCovector K L₀ φ z v) B.domain :=
    ((ContinuousLinearMap.apply ℂ ℂ v).restrictScalars ℝ).contDiff.comp_contDiffOn h₀
  have he₁ (v : HeckeCycles.GeometricSource.CM.BallChart) : ContDiffOn ℝ ∞ (fun z => Projection.CM.sourceThetaCovector K L₁ ψ z v) B.domain :=
    ((ContinuousLinearMap.apply ℂ ℂ v).restrictScalars ℝ).contDiff.comp_contDiffOn h₁
  unfold sourceWedgeCoefficient RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient sourceThetaCoordinates
  simp only [SparseSpanning.CM.jacobiCoefficients, LinearMap.coe_mk, AddHom.coe_mk]
  exact ((he₀ _).mul (he₁ _)).sub ((he₀ _).mul (he₁ _))

end

/-! The actual cotangent projection is evaluation of the Jacobi derivative
on explicit graph-frame slots, as required by ThetaKernel's tensor formula. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM _root_.Module

theorem jacobi_linear_duality {ι : Type*} [Fintype ι]
    (l : (ι → ℂ) →L[ℂ] ℂ) (m : (ι → ℂ) →ₗ[ℂ] ℂ) :
    m (SparseSpanning.CM.jacobiCoefficients ι l) = l (fun j => m ((Pi.basisFun ℂ ι) j)) := by
  have he (j : ι) : SparseSpanning.CM.jacobiCoefficients ι l j = l ((Pi.basisFun ℂ ι) j) := by
    change l (Pi.single j 1) = _
    apply congrArg l
    funext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  calc
    _ = ∑ j, SparseSpanning.CM.jacobiCoefficients ι l j * m ((Pi.basisFun ℂ ι) j) := by
      conv_lhs => rw [← (Pi.basisFun ℂ ι).sum_repr (SparseSpanning.CM.jacobiCoefficients ι l)]
      simp only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul]
    _ = ∑ j, m ((Pi.basisFun ℂ ι) j) * l ((Pi.basisFun ℂ ι) j) := by
      simp only [he, mul_comm]
    _ = l (fun j => m ((Pi.basisFun ℂ ι) j)) := by
      conv_rhs => rw [← (Pi.basisFun ℂ ι).sum_repr (fun j => m ((Pi.basisFun ℂ ι) j))]
      simp only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

def graphCoefficient (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →ₗ[ℂ] ℂ where
  toFun c := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) i.castSucc
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def thetaJacobiSlot (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    HeckeCycles.GeometricSource.CM.Positions K places → ℂ :=
  fun j => graphCoefficient K L z i ((Pi.basisFun ℂ (HeckeCycles.GeometricSource.CM.Positions K places)) j)

theorem source_coordinates_slots (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    sourceThetaCoordinates K L φ z i =
      (L.halfDet z : ℂ) * fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0 (thetaJacobiSlot K L z i) := by
  unfold thetaJacobiSlot
  rw [← jacobi_linear_duality (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0) (graphCoefficient K L z i)]
  unfold sourceThetaCoordinates
  rw [SparseSpanning.CM.source_covector_eq_projection]
  fin_cases i <;>
    simp [SparseSpanning.CM.jacobiCoefficients, SparseSpanning.CM.thetaCotangentProjection, SparseSpanning.CM.graphCotangentLinear,
      Projection.CM.graphCotangent, graphCoefficient]

theorem source_coordinates_completed_slots (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    sourceThetaCoordinates K L φ z i =
      (L.halfDet z : ℂ) * fderiv ℂ (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ (L.period z)) 0
        (thetaJacobiSlot K L z i) := by
  rw [source_coordinates_slots]
  have he : fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0 =
      fderiv ℂ (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ (L.period z)) 0 := by
    rw [HeckeCycles.Theta.Weil.CM.source_first_is_canonical]
    exact (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.first_derivatives_uncorrected_holomorphic φ (L.period z)).2.1.fderiv.symm
  rw [he]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots.CM
