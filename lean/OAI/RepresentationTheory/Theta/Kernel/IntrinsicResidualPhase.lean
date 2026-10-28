import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction

/-! # Intrinsic Residual Phase -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic

noncomputable section

/-! The residual difference between the given native phase coordinates
and the cotangent coordinates of its position map commutes with the
actual archimedean SU action. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic

theorem swapPhase_injective {I R : Type} : Function.Injective (Adelic.DataTheta.swapPhase (I := I) (R := R)) := by
  intro x y h
  funext i
  cases i with
  | inl i => exact congrFun h (.inr i)
  | inr i => exact congrFun h (.inl i)

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

def residualPhase (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m) :=
  B.realPhase.symm (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u)

theorem residual_phase_positions (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    (fun v i => residualPhase B u v (.inl i)) = fun v i => u v (.inl i) := by
  apply B.realPosition.injective
  funext i
  rw [← hC.2.2.2.2.1]
  change B.realPhase (B.realPhase.symm (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u)) (.inl i) = _
  rw [B.realPhase.apply_symm_apply]
  rfl

theorem residual_phase_commutes (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    residualPhase B (IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g u) =
      IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g (residualPhase B u) := by
  apply B.realPhase.injective
  apply swapPhase_injective
  have hnative := hC.2.2.2.2.2.2.2.1 g (residualPhase B u)
  change (Adelic.DataTheta.blockMatrix (B.symplectic g)).mulVec (Adelic.DataTheta.swapPhase (B.realPhase (residualPhase B u))) =
    Adelic.DataTheta.swapPhase (B.realPhase (IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g (residualPhase B u))) at hnative
  have hcot := IntrinsicCotangentAction.Intrinsic.native_cotangent_action B hO hG hψ g z u
  simp only [residualPhase,B.realPhase.apply_symm_apply] at hnative ⊢
  exact hcot.symm.trans hnative

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic
