import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison

/-! # Intrinsic Compact -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompact.IntrinsicKernel

noncomputable section

/-! Exact compact-chart/native completed-kernel comparison with a
constructed actual finite-Schwartz input. The rational phase transport
is independent of the ball point and Jacobi variable. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicCompletion
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison.IntrinsicKernel

theorem phase_weight_cancel {a b f g k l : ℂ} (hab : a * b = 1)
    (hg : g = a * f) (hl : l = b * k) : g * l = f * k := by
  calc
    _ = (a * f) * (b * k) := congrArg₂ (fun x y : ℂ => x * y) hg hl
    _ = (a * b) * (f * k) := by ring
    _ = _ := by rw [hab,one_mul]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_bare_kernel_comparison (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex A → ℂ) (x : Fin 6 → F) :
    Adelic.DataTheta.gaussianValue (Bp.period z).matrix ((Bp.frame z).invᵀ.mulVec u)
      (fun i => (Bp.rationalPosition x i : ℝ)) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
        Adelic.DataTheta.gaussianValue (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
          (((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u)
          (fun i => (B.rationalPosition x i : ℝ)) := by
  have hR : (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp).mulVec (fun i => (B.rationalPosition x i : ℂ)) =
      fun i => (Bp.rationalPosition x i : ℂ) := by
    erw [IntrinsicCompactPositionMatrices.Intrinsic.compact_position_matrix_apply p B Bp hC hCp,
      IntrinsicCompactPositionMatrices.Intrinsic.compact_position_rational p B Bp hC hCp]
    change (fun i => (Bp.rationalPosition (B.rationalPosition.symm (B.rationalPosition x)) i : ℂ)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hlin : (∑ i, ((Bp.rationalPosition x i : ℝ) : ℂ) * (Bp.frame z).invᵀ.mulVec u i) =
      ∑ i, ((B.rationalPosition x i : ℝ) : ℂ) *
        ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u i := by
    have h := Matrix.dotProduct_transpose_mulVec (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)
      (fun i => (B.rationalPosition x i : ℂ)) ((Bp.frame z).invᵀ.mulVec u)
    erw [← IntrinsicCompactZero.IntrinsicCompletion.compact_jacobi_relation p B Bp hC hCp hG hGp z u,hR] at h
    simp only [Complex.ofReal_ratCast]
    exact (h.trans (dotProduct_comm _ _)).symm
  have hq := IntrinsicCompactShear.Intrinsic.compact_quadratic_difference p B Bp hC hCp hG hGp z x
  have hq' : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (Bp.period z).matrix
      (fun i => (Bp.rationalPosition x i : ℝ)) (fun i => (Bp.rationalPosition x i : ℝ)) =
        AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
          (fun i => (B.rationalPosition x i : ℝ)) (fun i => (B.rationalPosition x i : ℝ)) +
            ((IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp x x : ℚ) : ℂ) := by linear_combination hq
  unfold Adelic.DataTheta.gaussianValue IntrinsicQuadraticPhase.Intrinsic.quadraticPhase
  erw [← Complex.exp_add,hq',hlin]
  congr 1
  ring

theorem compact_completed_kernel_of_weights (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hw : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x))
    (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.DataTheta.completedTheta Bp g (Bp.period z).matrix ((Bp.frame z).invᵀ.mulVec u) =
      Adelic.DataTheta.completedTheta B f (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
        (((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u) := by
  have ht : Adelic.DataTheta.rationalTheta Bp g (Bp.period z).matrix ((Bp.frame z).invᵀ.mulVec u) =
      Adelic.DataTheta.rationalTheta B f (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
        (((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u) := by
    apply tsum_congr
    intro x
    exact phase_weight_cancel (IntrinsicComparison.IntrinsicKernel.quadraticPhase_neg_mul 6 (IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x)
      (hw x) (compact_bare_kernel_comparison p B Bp hC hCp hG hGp z u x)
  exact congrArg₂ (fun x y : ℂ => x * y)
    (IntrinsicCompactZero.IntrinsicCompletion.compact_completion_comparison p B Bp hC hCp hG hGp z u) ht

theorem compact_completed_kernel_transport (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
      (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
      ∀ z u, Adelic.DataTheta.completedTheta Bp g (Bp.period z).matrix ((Bp.frame z).invᵀ.mulVec u) =
        Adelic.DataTheta.completedTheta B f (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
          (((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u) := by
  obtain ⟨g,hg⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp)
  exact ⟨g,hg,compact_completed_kernel_of_weights p B Bp hC hCp hG hGp f g hg⟩

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompact.IntrinsicKernel
