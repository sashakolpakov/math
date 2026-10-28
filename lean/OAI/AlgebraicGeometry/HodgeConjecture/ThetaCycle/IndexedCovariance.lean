import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReindexTheta
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis

/-! # Indexed Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance.CM

noncomputable section

/-! ThetaCycle: the constructed rational covariance in arbitrary finite
coordinates, including the actual total CM position space. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {I : Type*} [Fintype I] [DecidableEq I]

def indexedThetaMultiplier (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : ℂ :=
  NormalizedCovariance.CM.rationalThetaMultiplier (Fintype.card I) (OscillatorPhaseOrder.CM.reindexSymplectic (Fintype.equivFin I) γ)
    (ReindexTheta.CM.siegelReindex (Fintype.equivFin I) Z)

def indexedFiniteOscillatorInput (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I :=
  (ReindexTheta.CM.finiteInputReindex (Fintype.equivFin I)).symm
    (NormalizedCovariance.CM.normalizedFiniteOscillatorInput (Fintype.card I) (OscillatorPhaseOrder.CM.reindexSymplectic (Fintype.equivFin I) γ)
      (ReindexTheta.CM.finiteInputReindex (Fintype.equivFin I) φ))

theorem indexed_theta_multiplier_square (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    indexedThetaMultiplier γ Z ^ 2 = ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix).det :=
  (NormalizedCovariance.CM.rational_theta_multiplier_square _ _ _).trans (ReindexTheta.CM.reindex_rational_denominator_det _ γ Z)

theorem indexed_theta_multiplier_ne_zero (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    indexedThetaMultiplier γ Z ≠ 0 := ReindexTheta.CM.rational_theta_multiplier_ne_zero _ _ _

theorem indexed_completed_theta_covariance (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (indexedFiniteOscillatorInput γ φ) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) = indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z z := by
  let e := Fintype.equivFin I
  have h := NormalizedCovariance.CM.normalized_completed_theta_covariance (Fintype.card I) (OscillatorPhaseOrder.CM.reindexSymplectic e γ)
    (ReindexTheta.CM.finiteInputReindex e φ) (ReindexTheta.CM.siegelReindex e Z) (fun j => z (e.symm j))
  rw [ReindexTheta.CM.reindex_rational_siegel_action, ReindexTheta.CM.reindex_rational_jacobi_action, ReindexTheta.CM.completed_reindex] at h
  have he := ReindexTheta.CM.completed_reindex e (indexedFiniteOscillatorInput γ φ)
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)
  change RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed ((ReindexTheta.CM.finiteInputReindex e) ((ReindexTheta.CM.finiteInputReindex e).symm _)) _ _ = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he.symm.trans h

theorem indexed_theta_multiplier_holomorphic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [Nonempty I] (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) {s : Set V} (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s) :
    DifferentiableOn ℂ (fun x => indexedThetaMultiplier γ (Z x)) s := by
  apply ReindexTheta.CM.rational_theta_multiplier_holomorphic (Fintype.card I) Fintype.card_pos
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  change DifferentiableOn ℂ (fun x => (Z x).matrix ((Fintype.equivFin I).symm i)
    ((Fintype.equivFin I).symm j)) s
  fun_prop

theorem indexed_completed_jet_covariance (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (a : ℕ) (v : Fin a → (I → ℂ)) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (indexedFiniteOscillatorInput γ φ)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)) 0 (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i)) =
      indexedThetaMultiplier γ Z * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  let L := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z
  let Ψ := indexedFiniteOscillatorInput γ φ
  let W := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z
  have hf : ContDiff ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ W) :=
    (RepresentationTheory.Theta.Kernel.Analysis.adelic_analysis (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput I) Ψ W).2.of_le (by simp)
  have hg : ContDiffAt ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 :=
    ((RepresentationTheory.Theta.Kernel.Analysis.adelic_analysis (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput I) φ Z).2.of_le (by simp)).contDiffAt
  have he : (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ W) ∘ L = indexedThetaMultiplier γ Z • RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z :=
    funext (fun z => indexed_completed_theta_covariance γ φ Z z)
  have hd := congrArg (fun f => iteratedFDeriv ℂ a f 0 v) he
  rw [iteratedFDeriv_const_smul_apply hg, L.iteratedFDeriv_comp_right hf 0 le_rfl] at hd
  simpa only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    _root_.smul_apply, smul_eq_mul] using hd

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance.CM
