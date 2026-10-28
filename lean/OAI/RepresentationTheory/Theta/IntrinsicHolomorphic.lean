import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice
import OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus

/-! # Intrinsic Holomorphic -/

namespace OAI.RepresentationTheory.Theta.IntrinsicHolomorphic.OneFormsIntrinsic

noncomputable section

/-! Holomorphy of the literal AdelicTheta theta derivative and geometric projection. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise BoundedContinuousFunction

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

def ballExtension {V : Type} [Zero V] (f : Adelic.BallNatural.Ball → V) (z : Fin 2 → ℂ) : V :=
  if hz : z ∈ Adelic.BallGeometryData.ballDomain then f ⟨z, hz⟩ else 0

theorem ballHolomorphic_comp
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f : Adelic.BallNatural.Ball → V) (g : V → W) (hf : Adelic.BallGeometryData.BallHolomorphic f)
    (hg : ∀ z, DifferentiableAt ℂ g (f z)) :
    Adelic.BallGeometryData.BallHolomorphic (fun z => g (f z)) := by
  have hc : DifferentiableOn ℂ (fun z => g (ballExtension f z)) Adelic.BallGeometryData.ballDomain := by
    intro z hz
    apply DifferentiableAt.comp_differentiableWithinAt z _ (hf z hz)
    simpa only [ballExtension, dite_eq_left hz] using hg ⟨z, hz⟩
  exact hc.congr (fun z hz => by simp only [ballExtension, dite_eq_left hz])

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

local instance phaseNormedAddCommGroup :
    NormedAddCommGroup ((Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] ℂ) := inferInstance
local instance phaseNormedSpace :
    NormedSpace ℂ ((Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] ℂ) := inferInstance

theorem completed_first_weighted
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (L : Submodule ℤ (Adelic.BallGeometryData.FrameIndex A → ℝ)) [DiscreteTopology L]
    (φ : L →ᵇ ℂ)
    (hcomp : ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) ξ,
      Adelic.DataTheta.completedTheta B f Z.matrix ξ = Definitions.completedTheta L φ Z.matrix ξ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) :
    fderiv ℂ (Adelic.DataTheta.completedTheta B f Z.matrix) 0 =
      DerivativeFactorizationAdelicLattice.weightedFirst (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) L φ
        (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix) := by
  have hraw : Definitions.theta L φ Z.matrix =
      Z.phase.weightedThetaSeries (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) L φ := by
    funext ξ
    apply tsum_congr
    intro x
    simp [AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
  have hd := Z.phase.weightedThetaSeries_hasFDerivAt
    (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) L φ 0
  rw [← hraw] at hd
  have hc := AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero
    (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹)) hd
  rw [funext (hcomp Z)]
  refine hc.fderiv.trans ?_
  simp only [DerivativeFactorizationAdelicLattice.weightedFirst, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaSeriesDerivative,
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm_zero,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.gaussianWeight, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase]

theorem completed_first_holomorphic
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    Adelic.BallGeometryData.BallHolomorphic (fun z => fderiv ℂ (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0) := by
  obtain ⟨L, hL, φ, _, _, _, hcomp, _⟩ := hTheta.1 f
  let := hL
  have heq : (fun z => fderiv ℂ (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0) =
      fun z => DerivativeFactorizationAdelicLattice.weightedFirst (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) L φ
        (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix) := by
    funext z
    exact completed_first_weighted B f L φ (fun Z ξ => (hcomp Z ξ).2) (B.period z)
  rw [heq]
  apply ballHolomorphic_comp (fun z => (B.period z).matrix)
    (fun Z => DerivativeFactorizationAdelicLattice.weightedFirst (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) L φ
      (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z)) hGeometry.2.2.1
  intro z
  let T : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ →L[ℂ]
      ((Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) →L[ℝ] ℂ) :=
    (AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.thetaMatrixPhaseMap (ι := Adelic.BallGeometryData.FrameIndex A)).toLinearMap.toContinuousLinearMap
  exact (DerivativeFactorizationAdelicLattice.weightedFirst_differentiableAt (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A))
    L φ (B.period z).phase).comp (B.period z).matrix T.differentiableAt

variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A₁ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A₁)

theorem thetaOneForm_coefficients (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) :
    OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ f z = (B₁.halfFrame z)⁻¹ •
      ((fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f (B₁.period z).matrix) 0)
        (fun j => (B₁.frame z).inv (OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A₁) 0) j) • ContinuousLinearMap.proj 0 +
       (fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f (B₁.period z).matrix) 0)
        (fun j => (B₁.frame z).inv (OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A₁) 1) j) • ContinuousLinearMap.proj 1) := by
  ext u
  simp [OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm, OneFormsIntrinsicLattice.IntrinsicProjection.cotangentProjection, OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding, Matrix.mulVec_single, Matrix.row]
  ring

theorem thetaOneForm_holomorphic
    (hGeometry : Adelic.DataTheta.GeometryIdentification B₁) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B₁)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) : Adelic.BallGeometryData.BallHolomorphic (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ f) := by
  have hfirst := completed_first_holomorphic B₁ hGeometry hTheta f
  obtain ⟨_, _, _, hM, hh, hhalf, _⟩ := hGeometry
  let M := ballExtension (fun z => (B₁.frame z).val)
  let Hf := ballExtension B₁.halfFrame
  let L := ballExtension
    (fun z => fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f (B₁.period z).matrix) 0)
  have hL : DifferentiableOn ℂ L Adelic.BallGeometryData.ballDomain := hfirst
  have hInv : DifferentiableOn ℂ (fun z => (M z)⁻¹) Adelic.BallGeometryData.ballDomain :=
    AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_inverse_holomorphic M hM (by
      intro z hz
      change (ballExtension (fun z => (B₁.frame z).val) z).det ≠ 0
      simp only [ballExtension, dite_eq_left hz]
      rw [← (hhalf ⟨z, hz⟩).2]
      exact pow_ne_zero 2 (hhalf ⟨z, hz⟩).1)
  have hHi : DifferentiableOn ℂ (fun z => (Hf z)⁻¹) Adelic.BallGeometryData.ballDomain := hh.inv (by
    intro z hz
    simpa only [Hf, ballExtension, dite_eq_left hz] using (hhalf ⟨z, hz⟩).1)
  have hrow (i : Fin 2) : DifferentiableOn ℂ
      (fun z => fun j => (M z)⁻¹ (OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A₁) i) j) Adelic.BallGeometryData.ballDomain := by
    apply differentiableOn_pi.mpr
    intro j
    exact (differentiable_apply j).comp_differentiableOn
      ((differentiable_apply (OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A₁) i)).comp_differentiableOn hInv)
  have hc := hHi.smul
    (((hL.clm_apply (hrow 0)).smul (differentiableOn_const
      (ContinuousLinearMap.proj (0 : Fin 2) : OneFormsIntrinsicLattice.IntrinsicProjection.Cotangent))).add
      ((hL.clm_apply (hrow 1)).smul (differentiableOn_const
        (ContinuousLinearMap.proj (1 : Fin 2) : OneFormsIntrinsicLattice.IntrinsicProjection.Cotangent))))
  apply hc.congr
  intro z hz
  simp only [M, Hf, L, ballExtension, dite_eq_left hz]
  rw [thetaOneForm_coefficients]
  simp [hz]

end

end OAI.RepresentationTheory.Theta.IntrinsicHolomorphic.OneFormsIntrinsic
