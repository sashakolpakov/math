import OAI.RepresentationTheory.Theta.CompletionAnalysis
import OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification
import OAI.RepresentationTheory.Theta.Adelic.GaussianProduct
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness
import OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Intrinsic Regularity -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRegularity.IntrinsicTheta

noncomputable section

/-! Completed theta regularity directly from the proved lattice analysis.
No uncompleted transformation equation or CompletedTheta result-level input is used.
The rational lattice identification, period and half-frame are the existing
concrete constructions of the repaired AdelicTheta statement. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness
open OAI.RepresentationTheory.Theta.Adelic.SupportLattice OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

/-- Smoothness of the actual rational completed tensors, obtained by the
proved exact lattice reindexing and local analytic differentiation. -/
theorem completedTensor_smooth (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) :
    ContDiffOn ℝ ⊤ (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a) Definitions.siegelDomain := by
  have he := funext (LatticeIdentification.completedTensor_lattice A P f a)
  rw [he]
  exact CompletionAnalysis.completedTensor_smooth (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) a

/-- Symmetry is the symmetry of the actual iterated complex derivative. -/
theorem completedTensor_symmetric (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (σ : Equiv.Perm (Fin a))
    (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z.matrix (fun i => v (σ i)) =
      DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z.matrix v := by
  rw [LatticeIdentification.completedTensor_lattice]
  exact CompletionAnalysis.completedTensor_symmetric (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) a Z σ v

/-- Change to the constructed geometric Hodge and half-determinant frames. -/
theorem geometricTensor_smooth (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) :
    BallGeometryData.BallSmooth (DataTheta.geometricTensor (GeometricGaussians.constructedComparison A P) f a) := by
  let Z : (Fin 2 → ℂ) → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then (PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).matrix else 0
  let Q : (Fin 2 → ℂ) → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then (PeriodCoordinates.geometricPositionUnit A P ⟨z, hz⟩).inv else 0
  let c : (Fin 2 → ℂ) → ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then GeometricHalfFrame.geometricHalfFrame A P ⟨z, hz⟩ else 0
  have hZ : ContDiffOn ℝ ⊤ Z BallGeometryData.ballDomain := GeometricFrameSmoothness.period_matrix_smooth A P
  have hQ : ContDiffOn ℝ ⊤ Q BallGeometryData.ballDomain := GeometricFrameSmoothness.position_inverse_smooth A P
  have hc : ContDiffOn ℝ ⊤ c BallGeometryData.ballDomain := GeometricFrameSmoothness.half_frame_smooth A P
  have hm : Set.MapsTo Z BallGeometryData.ballDomain Definitions.siegelDomain := by
    intro z hz
    change (Z z).IsSymm ∧ Matrix.PosDef (fun i j => (Z z i j).im)
    simp only [Z, dite_eq_left hz]
    exact ⟨(PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).symmetric,
      (PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).imaginary_posDef⟩
  have hT := (completedTensor_smooth A P f a).comp hZ hm
  have hM := TensorSmoothness.matrixOperator_contDiff.comp_contDiffOn
    (TensorSmoothness.matrix_transpose_contDiff.comp_contDiffOn hQ)
  have ht := TensorSmoothness.tensor_frame_smooth a
    (fun z => DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (Z z))
    (fun z => (Matrix.toLin' (Q z)ᵀ).toContinuousLinearMap) hT hM
  have hn : ∀ z ∈ BallGeometryData.ballDomain, c z ≠ 0 := by
    intro z hz
    simp only [c, dite_eq_left hz]
    exact GeometricHalfFrame.geometricHalfFrame_nonzero A P ⟨z, hz⟩
  have hs : ContDiffOn ℝ ⊤ (fun z => (c z)⁻¹ •
      (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (Z z)).compContinuousLinearMap
        (fun _ => (Matrix.toLin' (Q z)ᵀ).toContinuousLinearMap)) BallGeometryData.ballDomain :=
    (hc.inv hn).smul ht
  apply hs.congr
  intro z hz
  simp only [Z, Q, c, dite_eq_left hz]
  rfl

/-- The entire concrete theta-construction conclusion, without a Poisson
or completed-theta prerequisite. Rational covariance is proved separately
from the actual oscillator operators, not assumed here. -/
theorem constructedComparison_theta : DataTheta.Descent.ThetaConstruction (GeometricGaussians.constructedComparison A P) :=
  ⟨LatticeIdentification.constructedComparison_lattice A P, LatticeIdentification.rationalTheta_summable A P,
    GaussianProduct.ThetaComparison.rationalTheta_native A P, completedTensor_smooth A P,
    completedTensor_symmetric A P, geometricTensor_smooth A P⟩

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRegularity.IntrinsicTheta
