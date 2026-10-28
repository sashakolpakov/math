import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices

/-! # Intrinsic Compact Shear -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic

noncomputable section

/-! The difference between a compact-action chart Gaussian and an
actual native chosen Gaussian is the rational shear of their proved
coordinate change. No coordinate alignment is imposed on the witnesses. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

def compactShearBilinear : (Fin 6 → F) →ₗ[ℚ] (Fin 6 → F) →ₗ[ℚ] ℚ :=
  (dotProductBilin ℚ ℚ).compl₁₂
    ((IntrinsicPositionMatrices.IntrinsicShearComparison.momenta ℚ _).comp ((IntrinsicCompactPhaseChange.Intrinsic.compactRationalPhaseChange p B Bp).toLinearMap.comp
      ((IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition ℚ _).comp B.rationalPosition.toLinearMap)))
    Bp.rationalPosition.toLinearMap

theorem compactShearBilinear_apply (x y : Fin 6 → F) :
    compactShearBilinear p B Bp x y = ∑ j,
      IntrinsicCompactPhaseChange.Intrinsic.compactRationalPhaseChange p B Bp
        (Sum.elim (B.rationalPosition x) (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) (.inr j) * Bp.rationalPosition y j := rfl

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_position_rational (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (q : Adelic.BallGeometryData.FrameIndex A → ℚ) :
    IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp (fun i => (q i : ℂ)) =
      fun i => (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp q i : ℂ) := by
  have he := IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp (Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ))
  have hc : (fun i => ((Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) i : ℂ)) =
      Sum.elim (fun i => (q i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Rat.cast_zero]
  rw [hc] at he
  funext i
  exact (congrFun he (.inl i)).trans (congrArg (fun r : ℚ => (r : ℂ))
    (IntrinsicCompactPhaseChange.Intrinsic.compact_rational_position p B Bp hC hCp (Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) i))

theorem compact_quadratic_difference (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (x : Fin 6 → F) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (Bp.period z).matrix
        (fun i => (Bp.rationalPosition x i : ℝ)) (fun i => (Bp.rationalPosition x i : ℝ)) -
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
        (fun i => (B.rationalPosition x i : ℝ)) (fun i => (B.rationalPosition x i : ℝ)) =
      ((compactShearBilinear p B Bp x x : ℚ) : ℂ) := by
  let q : Adelic.BallGeometryData.FrameIndex A → ℚ := B.rationalPosition x
  have hr := compact_position_rational p B Bp hC hCp q
  have hq : IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp q = Bp.rationalPosition x := by
    change Bp.rationalPosition (B.rationalPosition.symm (B.rationalPosition x)) = _
    rw [LinearEquiv.symm_apply_apply]
  erw [hq] at hr
  have h := IntrinsicPositionMatrices.IntrinsicShearComparison.quadratic_graph_difference (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap
    (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp) (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)) (Bp.period z).matrix
    (IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_pairing p B Bp hC hCp) (IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_positions p B Bp hC hCp)
    (IntrinsicCompactFrameComparison.IntrinsicGraph.compact_graph_in_positions p B Bp hC hCp hG hGp z) (fun i => (q i : ℂ))
  erw [hr] at h
  have he := IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp (Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ))
  have hc : (fun i => ((Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) i : ℂ)) =
      Sum.elim (fun i => (q i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Rat.cast_zero]
  rw [hc] at he
  erw [he] at h
  simpa only [IntrinsicPositionMatrices.IntrinsicShearComparison.siegelMatrixForm_as_dot,Complex.ofReal_ratCast,compactShearBilinear_apply,
    Rat.cast_sum,Rat.cast_mul] using h

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic
