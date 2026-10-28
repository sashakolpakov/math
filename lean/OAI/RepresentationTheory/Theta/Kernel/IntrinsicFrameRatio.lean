import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn

/-! # Intrinsic Frame Ratio -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameRatio.Intrinsic

noncomputable section

/-! The relative compact-action frame is independent of the ball point.
This uses locality of the actual position projection and the fact that
compact changes fix the distinguished place. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicVariation OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

theorem fixed_projection_frame_ratio {I : Type} [Fintype I] [DecidableEq I]
    (F₀ : (Matrix I I ℂ)ˣ) (F₁ H₀ H₁ P S : Matrix I I ℂ)
    (hF : S * F₀.val = F₀.val * P) (hH : S * H₀ = H₀ * P)
    (hfix : H₀ * P = F₀.val * P) (hvar : (F₁ - F₀.val) * P = F₁ - F₀.val)
    (hmove : H₁ - H₀ = F₁ - F₀.val) :
    F₁ * (F₀.inv * H₀) = H₁ := by
  have hproj : P * (F₀.inv * H₀) = P := by
    have he : F₀.val * (P * (F₀.inv * H₀)) = F₀.val * P := by
      calc
        _ = (F₀.val * P) * F₀.inv * H₀ := by simp only [Matrix.mul_assoc]
        _ = (S * F₀.val) * F₀.inv * H₀ := by rw [hF]
        _ = S * H₀ := by rw [Matrix.mul_assoc S,F₀.val_inv,Matrix.mul_one]
        _ = F₀.val * P := hH.trans hfix
    have hc := congrArg (fun M => F₀.inv * M) he
    simpa only [← Matrix.mul_assoc,F₀.inv_val,Matrix.one_mul] using hc
  have hdiff : (F₁ - F₀.val) * (F₀.inv * H₀) = F₁ - F₀.val := by
    calc
      _ = ((F₁ - F₀.val) * P) * (F₀.inv * H₀) := by rw [hvar]
      _ = (F₁ - F₀.val) * P := by rw [Matrix.mul_assoc,hproj]
      _ = F₁ - F₀.val := hvar
  have he : F₁ * (F₀.inv * H₀) - H₀ = H₁ - H₀ := by
    simpa only [Matrix.sub_mul,← Matrix.mul_assoc,F₀.val_inv,Matrix.one_mul] using
      hdiff.trans hmove.symm
  simpa only [sub_add_cancel] using congrArg (fun M => M + H₀) he

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem action_frame_ratio (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z w : Adelic.BallNatural.Ball) :
    (B.frame z).val * ((B.frame w).inv * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)) =
      IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) :=
  fixed_projection_frame_ratio (B.frame w) (B.frame z).val
    (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)) (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
    (IntrinsicFrameOn.IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished) (IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B A.distinguished)
    (IntrinsicFrameOn.IntrinsicPlaceProjection.native_frame_place B hC hG A.distinguished w) (IntrinsicFrameOn.IntrinsicPlaceProjection.action_frame_place B hC hG p A.distinguished w)
    (IntrinsicFrameOn.IntrinsicVariation.action_position_distinguished B hG p w) (IntrinsicFrameOn.IntrinsicVariation.native_position_variation B hG z w)
    (IntrinsicFrameOn.IntrinsicVariation.action_position_variation B hG p z w)

theorem action_position_determinant_constant (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hG : Adelic.DataTheta.GeometryIdentification B) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z w : Adelic.BallNatural.Ball) :
    (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).det =
      (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)).det := by
  have h := congrArg Matrix.det (action_frame_ratio B hC hG p z w)
  have hf (x : Adelic.BallNatural.Ball) : IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B x.val = (B.frame x).val := dite_eq_left x.property
  have hw : (B.frame w).inv.det * (B.frame w).val.det = 1 := by
    rw [← Matrix.det_mul,(B.frame w).inv_val,Matrix.det_one]
  have he : (B.frame z).val.det * (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)).det =
      (B.frame z).val.det * (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).det := by
    simp only [IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame,hf,Matrix.det_mul] at h
    calc
      _ = (B.frame z).val.det *
          ((IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)).det *
            ((B.frame w).inv.det * (B.frame w).val.det)) := by rw [hw,mul_one]
      _ = (B.frame z).val.det * ((B.frame w).inv.det *
          ((IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)).det * (B.frame w).val.det)) := by ring
      _ = (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).det * (B.frame z).val.det := h
      _ = _ := mul_comm _ _
  exact (mul_left_cancel₀ (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B.frame z)))) he).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameRatio.Intrinsic
