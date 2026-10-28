import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison

/-! # Intrinsic Compact Symplectic Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic

noncomputable section

/-! The physical compact-coordinate change preserves the native
position polarization and the complex trace symplectic pairing. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

def compactPositionLinear : (Adelic.BallGeometryData.FrameIndex A → ℂ) →ₗ[ℂ] (Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) → ℂ) :=
  (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _).comp ((IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap.comp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition ℂ _))

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_phase_momentum (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) :
    (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _).comp ((IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap.comp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum ℂ _)) = 0 := by
  apply IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexLinear_ext_rational
  intro x
  have he := IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℚ) x)
  have hc : (fun j => ((Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℚ) x) j : ℂ)) =
      Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (fun j => (x j : ℂ)) := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Rat.cast_zero]
  rw [hc] at he
  funext i
  have hi := congrFun he (.inl i)
  rw [IntrinsicCompactPhaseChange.Intrinsic.compact_rational_position p B Bp hC hCp] at hi
  change IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (fun j => (x j : ℂ))) (.inl i) =
    (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp 0 i : ℂ) at hi
  rw [map_zero] at hi
  change IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (fun j => (x j : ℂ))) (.inl i) = 0
  simpa only [Pi.zero_apply,Rat.cast_zero] using hi

theorem compact_phase_positions (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp x) =
      compactPositionLinear p B Bp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ x) := by
  have hx : x = IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition ℂ _ (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ x) + IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum ℂ _ (fun i => x (.inr i)) := by
    funext i
    cases i <;> simp [IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition,IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum,IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions]
  have hm := congrArg (fun L => L (fun i => x (.inr i))) (compact_phase_momentum p B Bp hC hCp)
  calc
    _ = IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp
        (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition ℂ _ (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ x) + IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum ℂ _ (fun i => x (.inr i)))) := by rw [← hx]
    _ = compactPositionLinear p B Bp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ x) +
        IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum ℂ _ (fun i => x (.inr i)))) := by
      rw [map_add,map_add]
      rfl
    _ = _ := by
      change _ + ((IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _).comp
        ((IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap.comp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedMomentum ℂ _))) (fun i => x (.inr i)) = _
      rw [hm,LinearMap.zero_apply,add_zero]

theorem compact_phase_pairing (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P)
    (x y : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    Adelic.DataTheta.standardPairing (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp x) (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp y) =
      Adelic.DataTheta.standardPairing x y := by
  let f := (IntrinsicSymplecticComparison.Intrinsic.pairingBilinear ℂ _).compl₁₂ (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap
    (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap
  have he : f = IntrinsicSymplecticComparison.Intrinsic.pairingBilinear ℂ _ := by
    apply IntrinsicSymplecticComparison.Intrinsic.linear_ext_rational
    intro u
    apply IntrinsicSymplecticComparison.Intrinsic.linear_ext_rational
    intro v
    change Adelic.DataTheta.standardPairing (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp (fun i => (u i : ℂ)))
      (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp (fun i => (v i : ℂ))) =
        Adelic.DataTheta.standardPairing (fun i => (u i : ℂ)) (fun i => (v i : ℂ))
    rw [IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp,
      IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp,IntrinsicSymplecticComparison.Intrinsic.pairing_cast,IntrinsicSymplecticComparison.Intrinsic.pairing_cast,
      IntrinsicCompactPhaseChange.Intrinsic.compact_rational_pairing p B Bp hC hCp]
  exact congrArg (fun L => L x y) he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
