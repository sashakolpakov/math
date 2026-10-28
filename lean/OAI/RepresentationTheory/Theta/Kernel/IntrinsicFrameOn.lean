import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison

/-! # Intrinsic Frame On -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection

/-! Locality of the actual native and compact-action position frames.
The coefficient and position projections are derived from the full
native coordinate and geometric identifications. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def framePlaceMatrix (v : Fin A.places) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  Matrix.diagonal (fun i => if i.1 = v then 1 else 0)

theorem frame_place_apply (v : Fin A.places) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) (i : Adelic.BallGeometryData.FrameIndex A) :
    (framePlaceMatrix A v).mulVec a i = if i.1 = v then a i else 0 := by
  rw [framePlaceMatrix,Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem geometric_frame_place (v : Fin A.places) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v (Adelic.BallGeometryData.geometricFrame A z a) =
      Adelic.BallGeometryData.geometricFrame A z ((framePlaceMatrix A v).mulVec a) := by
  funext w
  apply Prod.ext <;> funext ij
  all_goals
    by_cases hw : w = v
    · subst w
      simp [IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection,IntrinsicPlaceProjection.Intrinsic.placeProjection,Adelic.BallGeometryData.geometricFrame,frame_place_apply]
    · simp [IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection,IntrinsicPlaceProjection.Intrinsic.placeProjection,Adelic.BallGeometryData.geometricFrame,frame_place_apply,hw]

theorem compact_phase_place (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) (w : Adelic.BallGeometryData.ComplexPhase A) :
    IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v (IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase A p w) =
      IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase A p (IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v w) := by
  funext u
  apply Prod.ext <;> funext ij
  all_goals
    by_cases hu : u = v
    · subst u
      simp [IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection,IntrinsicPlaceProjection.Intrinsic.placeProjection,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase]
    · simp [IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection,IntrinsicPlaceProjection.Intrinsic.placeProjection,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,hu,
        Matrix.mulVec,dotProduct]

theorem moving_frame_place (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v (IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a) =
      IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z ((framePlaceMatrix A v).mulVec a) := by
  unfold IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame
  rw [compact_phase_place,geometric_frame_place]

variable {A} (B : Adelic.DataTheta.ComparisonData F H K A)

def positionPlaceMatrix (v : Fin A.places) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v)).map Complex.ofRealHom

theorem native_frame_positions (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (B.complexPhase.symm (Adelic.BallGeometryData.geometricFrame A z a)) = (B.frame z).val.mulVec a := by
  have h := congrArg B.complexPhase.symm (hG.2.2.2.2.2.2.1 z a)
  exact congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _) ((B.complexPhase.symm_apply_apply _).symm.trans h).symm

theorem moving_frame_positions (hG : Adelic.DataTheta.GeometryIdentification B) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (B.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a)) =
      (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a := by
  funext i
  exact (congrFun (IntrinsicCompactActionParameter.Intrinsic.coordinate_action_frame A B hG p z a) (.inl i)).symm.trans
    (IntrinsicCompactFrameComparison.Intrinsic.parameter_frame_apply B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p) z a i).symm

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem native_frame_place (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (v : Fin A.places) (z : Adelic.BallNatural.Ball) :
    positionPlaceMatrix B v * (B.frame z).val = (B.frame z).val * framePlaceMatrix A v := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  change (positionPlaceMatrix B v * (B.frame z).val).mulVec a =
    ((B.frame z).val * framePlaceMatrix A v).mulVec a
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v) ((B.frame z).val.mulVec a) = _
  rw [← native_frame_positions B hG,IntrinsicPositionProjection.Intrinsic.coordinate_positions_projection B hC,geometric_frame_place,
    native_frame_positions B hG]

theorem action_frame_place (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) (z : Adelic.BallNatural.Ball) :
    positionPlaceMatrix B v * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) =
      IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) * framePlaceMatrix A v := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  change (positionPlaceMatrix B v * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a =
    (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) * framePlaceMatrix A v).mulVec a
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v)
    ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a) = _
  rw [← moving_frame_positions B hG,IntrinsicPositionProjection.Intrinsic.coordinate_positions_projection B hC,moving_frame_place,
    moving_frame_positions B hG]

end RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection

namespace RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicVariation

/-! Only the distinguished-place columns of the actual Hodge frame
vary over the ball. Every compact frame choice fixes those columns. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

theorem geometric_frame_variation (z w : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.BallGeometryData.geometricFrame A z ((IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a) -
        Adelic.BallGeometryData.geometricFrame A w ((IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a) =
      Adelic.BallGeometryData.geometricFrame A z a - Adelic.BallGeometryData.geometricFrame A w a := by
  funext v
  apply Prod.ext <;> funext ij
  all_goals
    by_cases hv : v = A.distinguished
    · simp [Adelic.BallGeometryData.geometricFrame,IntrinsicPlaceProjection.frame_place_apply,hv]
    · simp [Adelic.BallGeometryData.geometricFrame,IntrinsicPlaceProjection.frame_place_apply,hv]

theorem moving_frame_distinguished (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball)
    (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z ((IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a) =
      Adelic.BallGeometryData.geometricFrame A z ((IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a) := by
  funext v
  apply Prod.ext <;> funext ij
  all_goals
    by_cases hv : v = A.distinguished
    · subst v
      simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,p.distinguished]
    · rcases ij with ⟨i,j⟩
      fin_cases j <;>
        simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,Adelic.BallGeometryData.geometricFrame,IntrinsicPlaceProjection.frame_place_apply,hv]

theorem moving_frame_variation (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z w : Adelic.BallNatural.Ball)
    (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a - IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p w a = Adelic.BallGeometryData.geometricFrame A z a - Adelic.BallGeometryData.geometricFrame A w a := by
  funext v
  apply Prod.ext <;> funext ij
  all_goals
    by_cases hv : v = A.distinguished
    · subst v
      simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,p.distinguished]
    · simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,Adelic.BallGeometryData.geometricFrame,hv,Matrix.mulVec,dotProduct]

variable {A} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem native_position_variation (hG : Adelic.DataTheta.GeometryIdentification B) (z w : Adelic.BallNatural.Ball) :
    ((B.frame z).val - (B.frame w).val) * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished =
      (B.frame z).val - (B.frame w).val := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  change (((B.frame z).val - (B.frame w).val) * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a =
    ((B.frame z).val - (B.frame w).val).mulVec a
  rw [← Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.sub_mulVec]
  rw [← IntrinsicPlaceProjection.native_frame_positions B hG,← IntrinsicPlaceProjection.native_frame_positions B hG,
    ← IntrinsicPlaceProjection.native_frame_positions B hG,← IntrinsicPlaceProjection.native_frame_positions B hG]
  rw [← map_sub,← map_sub,← map_sub,← map_sub,geometric_frame_variation]

theorem action_position_distinguished (hG : Adelic.DataTheta.GeometryIdentification B) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (z : Adelic.BallNatural.Ball) :
    IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished =
      (B.frame z).val * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  change (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a =
    ((B.frame z).val * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec a
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,← IntrinsicPlaceProjection.moving_frame_positions B hG,
    moving_frame_distinguished,IntrinsicPlaceProjection.native_frame_positions B hG]

theorem action_position_variation (hG : Adelic.DataTheta.GeometryIdentification B) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (z w : Adelic.BallNatural.Ball) :
    IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) - IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val) =
      (B.frame z).val - (B.frame w).val := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  change (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) -
    IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,w.val)).mulVec a =
      ((B.frame z).val - (B.frame w).val).mulVec a
  rw [Matrix.sub_mulVec,Matrix.sub_mulVec]
  rw [← IntrinsicPlaceProjection.moving_frame_positions B hG,← IntrinsicPlaceProjection.moving_frame_positions B hG,
    ← IntrinsicPlaceProjection.native_frame_positions B hG,← IntrinsicPlaceProjection.native_frame_positions B hG]
  rw [← map_sub,← map_sub,← map_sub,← map_sub,moving_frame_variation]

end RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicVariation

namespace RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicCompactSlots

/-! Compact frame changes leave the distinguished dual slots fixed in
the actual position coordinates. Thus the order-two top projection
depends on the moved Hodge subspace, not on its compact frame basis. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicVariation OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

theorem inverse_on_projection {I : Type} [Fintype I] [DecidableEq I]
    (F₀ : (Matrix I I ℂ)ˣ) (F₁ P S : Matrix I I ℂ) (h₁ : IsUnit F₁.det)
    (hF : S * F₀.val = F₀.val * P) (hH : S * F₁ = F₀.val * P) :
    P * F₁⁻¹ = P * F₀.inv := by
  have hleft : F₀.inv * S = P * F₁⁻¹ := by
    calc
      _ = F₀.inv * S * (F₁ * F₁⁻¹) := by rw [Matrix.mul_nonsing_inv _ h₁,Matrix.mul_one]
      _ = F₀.inv * (S * F₁) * F₁⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * F₁⁻¹ := by rw [hH,← Matrix.mul_assoc,F₀.inv_val,Matrix.one_mul]
  have hright : F₀.inv * S = P * F₀.inv := by
    calc
      _ = F₀.inv * S * (F₀.val * F₀.inv) := by rw [F₀.val_inv,Matrix.mul_one]
      _ = F₀.inv * (S * F₀.val) * F₀.inv := by simp only [Matrix.mul_assoc]
      _ = P * F₀.inv := by rw [hF,← Matrix.mul_assoc,F₀.inv_val,Matrix.one_mul]
  exact hleft.symm.trans hright

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

theorem frame_place_slot (r : Fin 2) (u : IntrinsicExterior.Intrinsic.Tangent) :
    (IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) = IntrinsicSecondProjection.Intrinsic.slotEmbedding r u := by
  funext i
  rw [IntrinsicPlaceProjection.frame_place_apply]
  by_cases hi : i.1 = A.distinguished
  · simp [hi]
  · have h₀ : i ≠ IntrinsicSecondProjection.Intrinsic.slot (A := A) 0 r := fun h => hi (congrArg Prod.fst h)
    have h₁ : i ≠ IntrinsicSecondProjection.Intrinsic.slot (A := A) 1 r := fun h => hi (congrArg Prod.fst h)
    simp [hi,IntrinsicSecondProjection.Intrinsic.slotEmbedding,h₀,h₁]

variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem action_inverse_distinguished (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished * (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ =
      IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished * (B.frame z).inv :=
  inverse_on_projection (B.frame z) (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))
    (IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished) (IntrinsicPlaceProjection.positionPlaceMatrix B A.distinguished)
    (isUnit_iff_ne_zero.mpr (IntrinsicCompactFrameComparison.Intrinsic.compact_frame_det_nonzero p B Bp hC hCp hG hGp z))
    (IntrinsicPlaceProjection.native_frame_place B hC hG A.distinguished z)
    ((IntrinsicPlaceProjection.action_frame_place B hC hG p A.distinguished z).trans (IntrinsicVariation.action_position_distinguished B hG p z))

theorem action_inverse_slot (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (r : Fin 2) (u : IntrinsicExterior.Intrinsic.Tangent) :
    ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) =
      (B.frame z).invᵀ.mulVec (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) := by
  have ht := congrArg Matrix.transpose (action_inverse_distinguished p B Bp hC hCp hG hGp z)
  simp only [Matrix.transpose_mul,IntrinsicPlaceProjection.framePlaceMatrix,Matrix.diagonal_transpose] at ht
  have he := congrArg (fun M => M.mulVec (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) r u)) ht
  change ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec
    (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) = ((B.frame z).invᵀ * IntrinsicPlaceProjection.framePlaceMatrix A A.distinguished).mulVec
      (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) at he
  simpa only [← Matrix.mulVec_mulVec,frame_place_slot] using he

end RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicCompactSlots

end

end OAI
